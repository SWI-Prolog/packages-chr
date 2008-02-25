################################################################
# Install CHR stuff for the MS-Windows build
# Author: Jan Wielemaker
# 
# Use:
#	nmake /f Makefile.mak
#	nmake /f Makefile.mak install
################################################################

PLHOME=..\..
!include $(PLHOME)\src\rules.mk
CFLAGS=$(CFLAGS) /D__SWI_PROLOG__
LIBDIR=$(PLBASE)\library
EXDIR=$(PKGDOC)\examples\chr
CHR=$(LIBDIR)\chr
PL="$(PLHOME)\bin\plcon.exe" -L80M -G50M -T20M

LIBPL=		chr_runtime.pl chr_op.pl chr_translate.pl chr_debug.pl \
		chr_messages.pl hprolog.pl pairlist.pl clean_code.pl \
		find.pl a_star.pl binomialheap.pl builtins.pl \
		chr_hashtable_store.pl listmap.pl guard_entailment.pl \
		chr_compiler_options.pl chr_compiler_utility.pl \
		chr_compiler_errors.pl \
		chr_integertable_store.pl \
		chr_support.dll
CHRPL=		chr_swi.pl
EXAMPLES=	chrfreeze.chr fib.chr gcd.chr primes.chr \
		bool.chr family.chr fibonacci.chr leq.chr listdom.chr \
		chrdif.chr


all:		chr_translate.pl chr_support.dll

chr_support.dll:	chr_support.obj
		$(LD) /dll /out:$@ $(LDFLAGS) chr_support.obj $(PLLIB)

chr_translate_bootstrap1.pl: chr_translate_bootstrap1.chr 
		$(PL) -q -f chr_swi_bootstrap.pl \
		      -g "chr_compile_step1('chr_translate_bootstrap1.chr','chr_translate_bootstrap1.pl'),halt" \
		      -t "halt(1)"
		$(PL) -q -f chr_swi_bootstrap.pl \
		      -g "chr_compile_step2('chr_translate_bootstrap1.chr','chr_translate_bootstrap1.pl'),halt" \
		      -t "halt(1)"

chr_translate_bootstrap2.pl: chr_translate_bootstrap2.chr chr_translate_bootstrap1.pl 
		$(PL) -q -f chr_swi_bootstrap.pl \
		      -g "chr_compile_step2('chr_translate_bootstrap2.chr','chr_translate_bootstrap2.pl'),halt" \
		      -t 'halt(1)'
		$(PL) -q -f chr_swi_bootstrap.pl \
		      -g "chr_compile_step3('chr_translate_bootstrap2.chr','chr_translate_bootstrap2.pl'),halt" \
		      -t 'halt(1)'

guard_entailment.pl: guard_entailment.chr chr_translate_bootstrap2.pl 
		$(PL) -q -f chr_swi_bootstrap.pl \
		      -g "chr_compile_step3('guard_entailment.chr','guard_entailment.pl'),halt" \
		      -t 'halt(1)'

chr_translate.pl: chr_translate.chr chr_translate_bootstrap2.pl guard_entailment.pl
		$(PL) -q -f chr_swi_bootstrap.pl \
		      -g "chr_compile_step3('chr_translate.chr','chr_translate.pl'),halt" \
		      -t 'halt(1)'
		$(PL) -p chr=. -q -f chr_swi_bootstrap.pl \
		      -g "chr_compile_step4('guard_entailment.chr','guard_entailment.pl'),halt" \
		      -t 'halt(1)'
		$(PL) -p chr=. -q -f chr_swi_bootstrap.pl \
		      -g "chr_compile_step4('chr_translate.chr','chr_translate.pl'),halt" \
		      -t 'halt(1)'

chr.pl:		chr_swi.pl
		copy chr_swi.pl chr.pl

check:		chr.pl
		$(PL) -q -f chr_test.pl -g test,halt -t 'halt(1)'


!IF "$(CFG)" == "rt"
install::
!ELSE
install::
		@if not exist "$(CHR)\$(NULL)" $(MKDIR) "$(CHR)"
		@for %f in ($(LIBPL)) do \
		    copy "%f" "$(CHR)"
		copy $(CHRPL) "$(LIBDIR)\chr.pl"
		copy README "$(CHR)\README.TXT"
		$(MAKEINDEX)
!ENDIF

html-install:	install-examples
pdf-install:	install-examples

install-examples::
		if not exist "$(EXDIR)/$(NULL)" $(MKDIR) "$(EXDIR)"
		cd examples & @for %f in ($(EXAMPLES)) do @copy %f "$(EXDIR)"

xpce-install::

uninstall::
		@for %f in ($(LIBPL)) do \
		    del "$(CHR)\%f"
		del "$(CHR)\README.TXT"
		del "$(LIBDIR)\chr.pl"
		$(MAKEINDEX)

clean::
		if exist *~ del *~
		-del chr.pl chr_translate.pl
		-del chr_translate_bootstrap1.pl chr_translate_bootstrap2.pl
		-del guard_entailment.pl

distclean:	clean


