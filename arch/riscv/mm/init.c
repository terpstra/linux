// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2012 Regents of the University of California
 * Copyright (C) 2019 Western Digital Corporation or its affiliates.
 */

#include <linux/init.h>
#include <linux/mm.h>
#include <linux/memblock.h>
#include <linux/initrd.h>
#include <linux/swap.h>
#include <linux/sizes.h>
#include <linux/of_fdt.h>
#include <linux/libfdt.h>
#include <linux/set_memory.h>
#ifdef CONFIG_RELOCATABLE
#include <linux/elf.h>
#endif

#include <asm/fixmap.h>
#include <asm/tlbflush.h>
#include <asm/sections.h>
#include <asm/soc.h>
#include <asm/io.h>
#include <asm/ptdump.h>

#include "../kernel/head.h"

#ifdef CONFIG_64BIT
u64 satp_mode = IS_ENABLED(CONFIG_MAXPHYSMEM_2GB) ?
				SATP_MODE_39 : SATP_MODE_48;
bool pgtable_l4_enabled = IS_ENABLED(CONFIG_MAXPHYSMEM_2GB) ? false : true;
#else
u64 satp_mode = SATP_MODE_32;
bool pgtable_l4_enabled;
#endif
EXPORT_SYMBOL(pgtable_l4_enabled);
EXPORT_SYMBOL(satp_mode);

unsigned long kernel_virt_addr;
EXPORT_SYMBOL(kernel_virt_addr);
#ifdef CONFIG_RELOCATABLE
unsigned long __page_offset = _AC(CONFIG_PAGE_OFFSET, UL);
EXPORT_SYMBOL(__page_offset);
#endif

unsigned long empty_zero_page[PAGE_SIZE / sizeof(unsigned long)]
							__page_aligned_bss;
EXPORT_SYMBOL(empty_zero_page);

extern char _start[];
void *dtb_early_va;

static void __init zone_sizes_init(void)
{
	unsigned long max_zone_pfns[MAX_NR_ZONES] = { 0, };

#ifdef CONFIG_ZONE_DMA32
	max_zone_pfns[ZONE_DMA32] = PFN_DOWN(min(4UL * SZ_1G,
			(unsigned long) PFN_PHYS(max_low_pfn)));
#endif
	max_zone_pfns[ZONE_NORMAL] = max_low_pfn;

	free_area_init(max_zone_pfns);
}

static void setup_zero_page(void)
{
	memset((void *)empty_zero_page, 0, PAGE_SIZE);
}

#if defined(CONFIG_MMU) && defined(CONFIG_DEBUG_VM)
static inline void print_mlk(char *name, unsigned long b, unsigned long t)
{
	pr_notice("%12s : 0x%08lx - 0x%08lx   (%4ld kB)\n", name, b, t,
		  (((t) - (b)) >> 10));
}

static inline void print_mlm(char *name, unsigned long b, unsigned long t)
{
	pr_notice("%12s : 0x%08lx - 0x%08lx   (%4ld MB)\n", name, b, t,
		  (((t) - (b)) >> 20));
}

static void print_vm_layout(void)
{
	pr_notice("Virtual kernel memory layout:\n");
	print_mlk("fixmap", (unsigned long)FIXADDR_START,
		  (unsigned long)FIXADDR_TOP);
	print_mlm("pci io", (unsigned long)PCI_IO_START,
		  (unsigned long)PCI_IO_END);
	print_mlm("vmemmap", (unsigned long)VMEMMAP_START,
		  (unsigned long)VMEMMAP_END);
	print_mlm("vmalloc", (unsigned long)VMALLOC_START,
		  (unsigned long)VMALLOC_END);
	print_mlm("lowmem", (unsigned long)PAGE_OFFSET,
		  (unsigned long)high_memory);
}
#else
static void print_vm_layout(void) { }
#endif /* CONFIG_DEBUG_VM */

void __init mem_init(void)
{
#ifdef CONFIG_FLATMEM
	BUG_ON(!mem_map);
#endif /* CONFIG_FLATMEM */

	high_memory = (void *)(__va(PFN_PHYS(max_low_pfn)));
	memblock_free_all();

	mem_init_print_info(NULL);
	print_vm_layout();
}

#ifdef CONFIG_BLK_DEV_INITRD
static void __init setup_initrd(void)
{
	unsigned long size;

	if (initrd_start >= initrd_end) {
		pr_info("initrd not found or empty");
		goto disable;
	}
	if (__pa_symbol(initrd_end) > PFN_PHYS(max_low_pfn)) {
		pr_err("initrd extends beyond end of memory");
		goto disable;
	}

	size = initrd_end - initrd_start;
	memblock_reserve(__pa_symbol(initrd_start), size);
	initrd_below_start_ok = 1;

	pr_info("Initial ramdisk at: 0x%p (%lu bytes)\n",
		(void *)(initrd_start), size);
	return;
disable:
	pr_cont(" - disabling initrd\n");
	initrd_start = 0;
	initrd_end = 0;
}
#endif /* CONFIG_BLK_DEV_INITRD */

static phys_addr_t dtb_early_pa __initdata;

void __init setup_bootmem(void)
{
	struct memblock_region *reg;
	phys_addr_t mem_size = 0;
	phys_addr_t vmlinux_end = __pa_symbol(&_end);
	phys_addr_t vmlinux_start = __pa_symbol(&_start);

	/* Find the memory region containing the kernel */
	for_each_memblock(memory, reg) {
		phys_addr_t end = reg->base + reg->size;

		if (reg->base <= vmlinux_start && vmlinux_end <= end) {
			mem_size = min(reg->size, (phys_addr_t)-PAGE_OFFSET);

			/*
			 * Remove memblock from the end of usable area to the
			 * end of region
			 */
			if (reg->base + mem_size < end)
				memblock_remove(reg->base + mem_size,
						end - reg->base - mem_size);
		}
	}
	BUG_ON(mem_size == 0);

	/* Reserve from the start of the kernel to the end of the kernel */
	memblock_reserve(vmlinux_start, vmlinux_end - vmlinux_start);

	set_max_mapnr(PFN_DOWN(mem_size));
	max_pfn = PFN_DOWN(memblock_end_of_DRAM());
	max_low_pfn = max_pfn;

#ifdef CONFIG_BLK_DEV_INITRD
	setup_initrd();
#endif /* CONFIG_BLK_DEV_INITRD */

	/*
	 * Avoid using early_init_fdt_reserve_self() since __pa() does
	 * not work for DTB pointers that are fixmap addresses
	 */
	memblock_reserve(dtb_early_pa, fdt_totalsize(dtb_early_va));

	early_init_fdt_scan_reserved_mem();
	memblock_allow_resize();
	memblock_dump_all();

	for_each_memblock(memory, reg) {
		unsigned long start_pfn = memblock_region_memory_base_pfn(reg);
		unsigned long end_pfn = memblock_region_memory_end_pfn(reg);

		memblock_set_node(PFN_PHYS(start_pfn),
				  PFN_PHYS(end_pfn - start_pfn),
				  &memblock.memory, 0);
	}
}

#ifdef CONFIG_MMU
/* Offset between linear mapping virtual address and kernel load address */
unsigned long va_pa_offset;
EXPORT_SYMBOL(va_pa_offset);
/* Offset between kernel mapping virtual address and kernel load address */
unsigned long va_kernel_pa_offset;
EXPORT_SYMBOL(va_kernel_pa_offset);
unsigned long pfn_base;
EXPORT_SYMBOL(pfn_base);

pgd_t swapper_pg_dir[PTRS_PER_PGD] __page_aligned_bss;
pgd_t trampoline_pg_dir[PTRS_PER_PGD] __page_aligned_bss;
pte_t fixmap_pte[PTRS_PER_PTE] __page_aligned_bss;
static bool mmu_enabled;

#define MAX_EARLY_MAPPING_SIZE	SZ_128M

pgd_t early_pg_dir[PTRS_PER_PGD] __initdata __aligned(PAGE_SIZE);

void __set_fixmap(enum fixed_addresses idx, phys_addr_t phys, pgprot_t prot)
{
	unsigned long addr = __fix_to_virt(idx);
	pte_t *ptep;

	BUG_ON(idx <= FIX_HOLE || idx >= __end_of_fixed_addresses);

	ptep = &fixmap_pte[pte_index(addr)];

	if (pgprot_val(prot)) {
		set_pte(ptep, pfn_pte(phys >> PAGE_SHIFT, prot));
	} else {
		pte_clear(&init_mm, addr, ptep);
		local_flush_tlb_page(addr);
	}
}

static pte_t *__init get_pte_virt(phys_addr_t pa)
{
	if (mmu_enabled) {
		clear_fixmap(FIX_PTE);
		return (pte_t *)set_fixmap_offset(FIX_PTE, pa);
	} else {
		return (pte_t *)((uintptr_t)pa);
	}
}

static phys_addr_t __init alloc_pte(uintptr_t va)
{
	/*
	 * We only create PMD or PGD early mappings so we
	 * should never reach here with MMU disabled.
	 */
	BUG_ON(!mmu_enabled);

	return memblock_phys_alloc(PAGE_SIZE, PAGE_SIZE);
}

static void __init create_pte_mapping(pte_t *ptep,
				      uintptr_t va, phys_addr_t pa,
				      phys_addr_t sz, pgprot_t prot)
{
	uintptr_t pte_idx = pte_index(va);

	BUG_ON(sz != PAGE_SIZE);

	if (pte_none(ptep[pte_idx]))
		ptep[pte_idx] = pfn_pte(PFN_DOWN(pa), prot);
}

#ifndef __PAGETABLE_PMD_FOLDED

pud_t trampoline_pud[PTRS_PER_PUD] __page_aligned_bss;
pmd_t trampoline_pmd[PTRS_PER_PMD] __page_aligned_bss;
pud_t fixmap_pud[PTRS_PER_PUD] __page_aligned_bss;
pmd_t fixmap_pmd[PTRS_PER_PMD] __page_aligned_bss;
pmd_t early_pmd[PTRS_PER_PMD] __initdata __aligned(PAGE_SIZE);
pud_t early_pud[PTRS_PER_PUD] __initdata __aligned(PAGE_SIZE);

static pmd_t *__init get_pmd_virt(phys_addr_t pa)
{
	if (mmu_enabled) {
		clear_fixmap(FIX_PMD);
		return (pmd_t *)set_fixmap_offset(FIX_PMD, pa);
	} else {
		return (pmd_t *)((uintptr_t)pa);
	}
}

static phys_addr_t __init alloc_pmd(uintptr_t va)
{
	if (mmu_enabled)
		return memblock_phys_alloc(PAGE_SIZE, PAGE_SIZE);

	/* Only one PMD is available for early mapping */
	BUG_ON((va - kernel_virt_addr) >> PUD_SHIFT);

	return (uintptr_t)early_pmd;
}

static void __init create_pmd_mapping(pmd_t *pmdp,
				      uintptr_t va, phys_addr_t pa,
				      phys_addr_t sz, pgprot_t prot)
{
	pte_t *ptep;
	phys_addr_t pte_phys;
	uintptr_t pmd_idx = pmd_index(va);

	if (sz == PMD_SIZE) {
		if (pmd_none(pmdp[pmd_idx]))
			pmdp[pmd_idx] = pfn_pmd(PFN_DOWN(pa), prot);
		return;
	}

	if (pmd_none(pmdp[pmd_idx])) {
		pte_phys = alloc_pte(va);
		pmdp[pmd_idx] = pfn_pmd(PFN_DOWN(pte_phys), PAGE_TABLE);
		ptep = get_pte_virt(pte_phys);
		memset(ptep, 0, PAGE_SIZE);
	} else {
		pte_phys = PFN_PHYS(_pmd_pfn(pmdp[pmd_idx]));
		ptep = get_pte_virt(pte_phys);
	}

	create_pte_mapping(ptep, va, pa, sz, prot);
}

static pud_t *__init get_pud_virt(phys_addr_t pa)
{
	if (mmu_enabled) {
		clear_fixmap(FIX_PUD);
		return (pud_t *)set_fixmap_offset(FIX_PUD, pa);
	} else {
		return (pud_t *)((uintptr_t)pa);
	}
}

static phys_addr_t __init alloc_pud(uintptr_t va)
{
	if (mmu_enabled)
		return memblock_phys_alloc(PAGE_SIZE, PAGE_SIZE);

	/* Only one PUD is available for early mapping */
	BUG_ON((va - kernel_virt_addr) >> PGDIR_SHIFT);

	return (uintptr_t)early_pud;
}

static void __init create_pud_mapping(pud_t *pudp,
				      uintptr_t va, phys_addr_t pa,
				      phys_addr_t sz, pgprot_t prot)
{
	pmd_t *nextp;
	phys_addr_t next_phys;
	uintptr_t pud_index = pud_index(va);

	if (sz == PUD_SIZE) {
		if (pud_val(pudp[pud_index]) == 0)
			pudp[pud_index] = pfn_pud(PFN_DOWN(pa), prot);
		return;
	}

	if (pud_val(pudp[pud_index]) == 0) {
		next_phys = alloc_pmd(va);
		pudp[pud_index] = pfn_pud(PFN_DOWN(next_phys), PAGE_TABLE);
		nextp = get_pmd_virt(next_phys);
		memset(nextp, 0, PAGE_SIZE);
	} else {
		next_phys = PFN_PHYS(_pud_pfn(pudp[pud_index]));
		nextp = get_pmd_virt(next_phys);
	}

	create_pmd_mapping(nextp, va, pa, sz, prot);
}

#define pgd_next_t		pud_t
#define alloc_pgd_next(__va)	alloc_pud(__va)
#define get_pgd_next_virt(__pa)	get_pud_virt(__pa)
#define create_pgd_next_mapping(__nextp, __va, __pa, __sz, __prot)	\
	create_pud_mapping(__nextp, __va, __pa, __sz, __prot)
#define fixmap_pgd_next		(pgtable_l4_enabled ?			\
			(uintptr_t)fixmap_pud : (uintptr_t)fixmap_pmd)
#define trampoline_pgd_next	(pgtable_l4_enabled ?			\
			(uintptr_t)trampoline_pud : (uintptr_t)trampoline_pmd)
#else
#define pgd_next_t		pte_t
#define alloc_pgd_next(__va)	alloc_pte(__va)
#define get_pgd_next_virt(__pa)	get_pte_virt(__pa)
#define create_pgd_next_mapping(__nextp, __va, __pa, __sz, __prot)	\
	create_pte_mapping(__nextp, __va, __pa, __sz, __prot)
#define fixmap_pgd_next		((uintptr_t)fixmap_pte)
#endif

static void __init create_pgd_mapping(pgd_t *pgdp,
				      uintptr_t va, phys_addr_t pa,
				      phys_addr_t sz, pgprot_t prot)
{
	pgd_next_t *nextp;
	phys_addr_t next_phys;
	uintptr_t pgd_idx = pgd_index(va);

#ifndef __PAGETABLE_PMD_FOLDED
	if (!pgtable_l4_enabled) {
		create_pud_mapping((pud_t *)pgdp, va, pa, sz, prot);
		return;
	}
#endif

	if (sz == PGDIR_SIZE) {
		if (pgd_val(pgdp[pgd_idx]) == 0)
			pgdp[pgd_idx] = pfn_pgd(PFN_DOWN(pa), prot);
		return;
	}

	if (pgd_val(pgdp[pgd_idx]) == 0) {
		next_phys = alloc_pgd_next(va);
		pgdp[pgd_idx] = pfn_pgd(PFN_DOWN(next_phys), PAGE_TABLE);
		nextp = get_pgd_next_virt(next_phys);
		memset(nextp, 0, PAGE_SIZE);
	} else {
		next_phys = PFN_PHYS(_pgd_pfn(pgdp[pgd_idx]));
		nextp = get_pgd_next_virt(next_phys);
	}

	create_pgd_next_mapping(nextp, va, pa, sz, prot);
}

static uintptr_t __init best_map_size(phys_addr_t base, phys_addr_t size)
{
	/* Upgrade to PMD_SIZE mappings whenever possible */
	if ((base & (PMD_SIZE - 1)) || (size & (PMD_SIZE - 1)))
		return PAGE_SIZE;

	return PMD_SIZE;
}

/*
 * setup_vm() is called from head.S with MMU-off.
 *
 * Following requirements should be honoured for setup_vm() to work
 * correctly:
 * 1) It should use PC-relative addressing for accessing kernel symbols.
 *    To achieve this we always use GCC cmodel=medany.
 * 2) The compiler instrumentation for FTRACE will not work for setup_vm()
 *    so disable compiler instrumentation when FTRACE is enabled.
 *
 * Currently, the above requirements are honoured by using custom CFLAGS
 * for init.o in mm/Makefile.
 */

#ifndef __riscv_cmodel_medany
#error "setup_vm() is called from head.S before relocate so it should not use absolute addressing."
#endif

#ifdef CONFIG_RELOCATABLE
extern unsigned long __rela_dyn_start, __rela_dyn_end;

#ifdef CONFIG_64BIT
#define Elf_Rela Elf64_Rela
#define Elf_Addr Elf64_Addr
#else
#define Elf_Rela Elf32_Rela
#define Elf_Addr Elf32_Addr
#endif

void __init relocate_kernel(uintptr_t load_pa)
{
	Elf_Rela *rela = (Elf_Rela *)&__rela_dyn_start;
	/*
	 * This holds the offset between the linked virtual address and the
	 * relocated virtual address.
	 */
	uintptr_t reloc_offset = kernel_virt_addr - KERNEL_LINK_ADDR;
	/*
	 * This holds the offset between kernel linked virtual address and
	 * physical address.
	 */
	uintptr_t va_kernel_link_pa_offset = KERNEL_LINK_ADDR - load_pa;

	for ( ; rela < (Elf_Rela *)&__rela_dyn_end; rela++) {
		Elf_Addr addr = (rela->r_offset - va_kernel_link_pa_offset);
		Elf_Addr relocated_addr = rela->r_addend;

		if (rela->r_info != R_RISCV_RELATIVE)
			continue;

		/*
		 * Make sure to not relocate vdso symbols like rt_sigreturn
		 * which are linked from the address 0 in vmlinux since
		 * vdso symbol addresses are actually used as an offset from
		 * mm->context.vdso in VDSO_OFFSET macro.
		 */
		if (relocated_addr >= KERNEL_LINK_ADDR)
			relocated_addr += reloc_offset;

		*(Elf_Addr *)addr = relocated_addr;
	}
}

#if defined(CONFIG_64BIT) && !defined(CONFIG_MAXPHYSMEM_2GB)
void disable_pgtable_l4(void)
{
	pgtable_l4_enabled = false;
	__page_offset = PAGE_OFFSET_L3;
	satp_mode = SATP_MODE_39;
}

/* There is a simple way to determine if 4-level is supported by the
 * underlying hardware: establish 1:1 mapping in 4-level page table mode
 * then read SATP to see if the configuration was taken into account
 * meaning sv48 is supported.
 */
asmlinkage __init void set_satp_mode(uintptr_t load_pa)
{
	u64 identity_satp, hw_satp;

	create_pgd_mapping(early_pg_dir, load_pa, (uintptr_t)early_pud,
			   PGDIR_SIZE, PAGE_TABLE);
	create_pud_mapping(early_pud, load_pa, (uintptr_t)early_pmd,
			   PUD_SIZE, PAGE_TABLE);
	create_pmd_mapping(early_pmd, load_pa, load_pa,
			   PMD_SIZE, PAGE_KERNEL_EXEC);

	identity_satp = PFN_DOWN((uintptr_t)&early_pg_dir) | satp_mode;
	local_flush_tlb_all();
	csr_write(CSR_SATP, identity_satp);

	hw_satp = csr_read(CSR_SATP);
	csr_write(CSR_SATP, 0ULL);
	local_flush_tlb_all();

	if (hw_satp != identity_satp)
		disable_pgtable_l4();

	memset(early_pg_dir, 0, PAGE_SIZE);
	memset(early_pud, 0, PAGE_SIZE);
	memset(early_pmd, 0, PAGE_SIZE);
}
#endif
#endif

static uintptr_t load_pa, load_sz;

static void __init create_kernel_page_table(pgd_t *pgdir, uintptr_t map_size)
{
	uintptr_t va, end_va;

	end_va = kernel_virt_addr + load_sz;
	for (va = kernel_virt_addr; va < end_va; va += map_size)
		create_pgd_mapping(pgdir, va,
				   load_pa + (va - kernel_virt_addr),
				   map_size, PAGE_KERNEL_EXEC);
}

asmlinkage void __init setup_vm(uintptr_t dtb_pa)
{
	uintptr_t va, end_va;
	uintptr_t map_size = best_map_size(load_pa, MAX_EARLY_MAPPING_SIZE);

	load_pa = (uintptr_t)(&_start);
	load_sz = (uintptr_t)(&_end) - load_pa;

#if defined(CONFIG_64BIT) && !defined(CONFIG_MAXPHYSMEM_2GB)
	set_satp_mode(load_pa);
#endif

	kernel_virt_addr = KERNEL_VIRT_ADDR;

	va_pa_offset = PAGE_OFFSET - load_pa;
	va_kernel_pa_offset = kernel_virt_addr - load_pa;
	pfn_base = PFN_DOWN(load_pa);

#ifdef CONFIG_RELOCATABLE
#ifdef CONFIG_64BIT
	/*
	 * Early page table uses only one PGDIR, which makes it possible
	 * to map PGDIR_SIZE aligned on PGDIR_SIZE: if the relocation offset
	 * makes the kernel cross over a PGDIR_SIZE boundary, raise a bug
	 * since a part of the kernel would not get mapped.
	 * This cannot happen on rv32 as we use the entire page directory level.
	 */
	BUG_ON(PGDIR_SIZE - (kernel_virt_addr & (PGDIR_SIZE - 1)) < load_sz);
#endif
	relocate_kernel(load_pa);
#endif
	/*
	 * Enforce boot alignment requirements of RV32 and
	 * RV64 by only allowing PMD or PGD mappings.
	 */
	BUG_ON(map_size == PAGE_SIZE);

	/* Sanity check alignment and size */
	BUG_ON((PAGE_OFFSET % PGDIR_SIZE) != 0);
	BUG_ON((load_pa % map_size) != 0);
	BUG_ON(load_sz > MAX_EARLY_MAPPING_SIZE);

	/* Setup early PGD for fixmap */
	create_pgd_mapping(early_pg_dir, FIXADDR_START,
			   fixmap_pgd_next, PGDIR_SIZE, PAGE_TABLE);

#ifndef __PAGETABLE_PMD_FOLDED
	/* Setup fixmap PUD and PMD */
	if (pgtable_l4_enabled)
		create_pud_mapping(fixmap_pud, FIXADDR_START,
			   (uintptr_t)fixmap_pmd, PUD_SIZE, PAGE_TABLE);
	create_pmd_mapping(fixmap_pmd, FIXADDR_START,
			   (uintptr_t)fixmap_pte, PMD_SIZE, PAGE_TABLE);

	/* Setup trampoline PGD and PMD */
	create_pgd_mapping(trampoline_pg_dir, kernel_virt_addr,
			   trampoline_pgd_next, PGDIR_SIZE, PAGE_TABLE);
	if (pgtable_l4_enabled)
		create_pud_mapping(trampoline_pud, kernel_virt_addr,
			   (uintptr_t)trampoline_pmd, PUD_SIZE, PAGE_TABLE);
	create_pmd_mapping(trampoline_pmd, kernel_virt_addr,
			   load_pa, PMD_SIZE, PAGE_KERNEL_EXEC);
#else
	/* Setup trampoline PGD */
	create_pgd_mapping(trampoline_pg_dir, kernel_virt_addr,
			   load_pa, PGDIR_SIZE, PAGE_KERNEL_EXEC);
#endif

	/*
	 * Setup early PGD covering entire kernel which will allow
	 * us to reach paging_init(). We map all memory banks later
	 * in setup_vm_final() below.
	 */
	create_kernel_page_table(early_pg_dir, map_size);

	/* Create fixed mapping for early FDT parsing */
	end_va = __fix_to_virt(FIX_FDT) + FIX_FDT_SIZE;
	for (va = __fix_to_virt(FIX_FDT); va < end_va; va += PAGE_SIZE)
		create_pte_mapping(fixmap_pte, va,
				   dtb_pa + (va - __fix_to_virt(FIX_FDT)),
				   PAGE_SIZE, PAGE_KERNEL);

	/* Save pointer to DTB for early FDT parsing */
	dtb_early_va = (void *)fix_to_virt(FIX_FDT) + (dtb_pa & ~PAGE_MASK);
	/* Save physical address for memblock reservation */
	dtb_early_pa = dtb_pa;
}

static void __init setup_vm_final(void)
{
	uintptr_t va, map_size;
	phys_addr_t pa, start, end;
	struct memblock_region *reg;
	static struct vm_struct vm_kernel = { 0 };

	/* Set mmu_enabled flag */
	mmu_enabled = true;

	/* Setup swapper PGD for fixmap */
	create_pgd_mapping(swapper_pg_dir, FIXADDR_START,
			   __pa_symbol(fixmap_pgd_next),
			   PGDIR_SIZE, PAGE_TABLE);

	/* Map all memory banks */
	for_each_memblock(memory, reg) {
		start = reg->base;
		end = start + reg->size;

		if (start >= end)
			break;
		if (memblock_is_nomap(reg))
			continue;
		if (start <= __pa(PAGE_OFFSET) &&
		    __pa(PAGE_OFFSET) < end)
			start = __pa(PAGE_OFFSET);

		map_size = best_map_size(start, end - start);
		for (pa = start; pa < end; pa += map_size) {
			va = (uintptr_t)__va(pa);
			create_pgd_mapping(swapper_pg_dir, va, pa,
					   map_size, PAGE_KERNEL);
		}
	}

	/* Map the kernel */
	create_kernel_page_table(swapper_pg_dir, PMD_SIZE);

	/* Reserve the vmalloc area occupied by the kernel */
	vm_kernel.addr = (void *)kernel_virt_addr;
	vm_kernel.phys_addr = load_pa;
	vm_kernel.size = (load_sz + PMD_SIZE - 1) & ~(PMD_SIZE - 1);
	vm_kernel.flags = VM_MAP | VM_NO_GUARD;
	vm_kernel.caller = __builtin_return_address(0);

	vm_area_add_early(&vm_kernel);

	/* Clear fixmap page table mappings */
	clear_fixmap(FIX_PTE);
	clear_fixmap(FIX_PMD);
	clear_fixmap(FIX_PUD);

	/* Move to swapper page table */
	csr_write(CSR_SATP, PFN_DOWN(__pa_symbol(swapper_pg_dir)) | satp_mode);
	local_flush_tlb_all();
}
#else
asmlinkage void __init setup_vm(uintptr_t dtb_pa)
{
#ifdef CONFIG_BUILTIN_DTB
	dtb_early_va = soc_lookup_builtin_dtb();
	if (!dtb_early_va) {
		/* Fallback to first available DTS */
		dtb_early_va = (void *) __dtb_start;
	}
#else
	dtb_early_va = (void *)dtb_pa;
#endif
}

static inline void setup_vm_final(void)
{
}
#endif /* CONFIG_MMU */

#ifdef CONFIG_STRICT_KERNEL_RWX
void mark_rodata_ro(void)
{
	unsigned long text_start = (unsigned long)_text;
	unsigned long text_end = (unsigned long)_etext;
	unsigned long rodata_start = (unsigned long)__start_rodata;
	unsigned long data_start = (unsigned long)_data;
	unsigned long max_low = (unsigned long)(__va(PFN_PHYS(max_low_pfn)));

	set_memory_ro(text_start, (text_end - text_start) >> PAGE_SHIFT);
	set_memory_ro(rodata_start, (data_start - rodata_start) >> PAGE_SHIFT);
	set_memory_nx(rodata_start, (data_start - rodata_start) >> PAGE_SHIFT);
	set_memory_nx(data_start, (max_low - data_start) >> PAGE_SHIFT);

	debug_checkwx();
}
#endif

void __init paging_init(void)
{
	setup_vm_final();
	memblocks_present();
	sparse_init();
	setup_zero_page();
	zone_sizes_init();
}

#ifdef CONFIG_SPARSEMEM_VMEMMAP
int __meminit vmemmap_populate(unsigned long start, unsigned long end, int node,
			       struct vmem_altmap *altmap)
{
	return vmemmap_populate_basepages(start, end, node);
}
#endif
