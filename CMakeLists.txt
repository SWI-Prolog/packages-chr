cmake_minimum_required(VERSION 2.8.12)
project(swipl-chr)

include("../cmake/PrologPackage.cmake")

set(CHR_SOURCES chr_runtime.pl chr_op.pl chr_debug.pl
    chr_messages.pl pairlist.pl clean_code.pl find.pl a_star.pl
    binomialheap.pl builtins.pl chr_hashtable_store.pl listmap.pl
    chr_compiler_options.pl chr_compiler_utility.pl
    chr_compiler_errors.pl chr_integertable_store.pl)
set(CHR_SOURCES_GENERATED guard_entailment.pl chr_translate.pl)

set(CHR_EXAMPLES chrfreeze.chr fib.chr gcd.chr primes.chr bool.chr
    family.chr fibonacci.chr leq.chr listdom.chr chrdif.chr)
prepend(CHR_EXAMPLES Examples/ ${CHR_EXAMPLES})

function(chr_bootstrap step file cmd)
  set(from ${CMAKE_CURRENT_SOURCE_DIR}/${file}.chr)
  set(to   ${file}.pl)
  set(${cmd} -f none -s ${CMAKE_CURRENT_SOURCE_DIR}/chr_swi_bootstrap.pl
	     -p chr=${CMAKE_CURRENT_SOURCE_DIR}:${CMAKE_CURRENT_BINARY_DIR}
             -g "\"chr_compile_step${step}('${from}','${to}')\""
	     -t halt
     PARENT_SCOPE)
endfunction()

# Generate chr_translate_bootstrap1.pl
chr_bootstrap(1
	      chr_translate_bootstrap1
	      CMD_1a)
chr_bootstrap(2
	      chr_translate_bootstrap1
	      CMD_1b)
# Generate chr_translate_bootstrap2.pl
chr_bootstrap(2
	      chr_translate_bootstrap2
	      CMD_2a)
chr_bootstrap(3
	      chr_translate_bootstrap2
	      CMD_2b)
# Generate guard_entailment.pl
chr_bootstrap(3
	      guard_entailment
	      CMD_3)
# Generate chr_translate.pl
chr_bootstrap(3
	      chr_translate
	      CMD_4a)
chr_bootstrap(4
	      guard_entailment
	      CMD_4b)
chr_bootstrap(4
	      chr_translate
	      CMD_4c)

add_custom_command(
    OUTPUT chr_translate_bootstrap1.pl
    COMMAND swipl ${CMD_1a}
    COMMAND swipl ${CMD_1b}
    DEPENDS chr_translate_bootstrap1.chr chr_translate_bootstrap.pl)
add_custom_command(
    OUTPUT chr_translate_bootstrap2.pl
    COMMAND swipl ${CMD_2a}
    COMMAND swipl ${CMD_2b}
    DEPENDS chr_translate_bootstrap2.chr chr_translate_bootstrap1.pl)
add_custom_command(
    OUTPUT guard_entailment.pl
    COMMAND swipl ${CMD_3}
    DEPENDS guard_entailment.chr chr_translate_bootstrap2.pl)
add_custom_command(
    OUTPUT chr_translate.pl
    COMMAND swipl ${CMD_4a}
    COMMAND swipl ${CMD_4b}
    COMMAND swipl ${CMD_4c}
    DEPENDS chr_translate.chr chr_translate_bootstrap2.pl guard_entailment.pl)
add_custom_command(
    OUTPUT chr.pl
    COMMAND cp -p ${CMAKE_CURRENT_SOURCE_DIR}/chr_swi.pl chr.pl
    DEPENDS chr_swi.pl)

add_custom_target(
    chr_compile ALL
    DEPENDS ${CHR_SOURCES_GENERATED} chr.pl)

prepend(CHR_SOURCES_GENERATED ${CMAKE_CURRENT_BINARY_DIR} ${CHR_SOURCES_GENERATED})
swipl_plugin(chr_priv
	     PL_LIB_SUBDIR chr
	     PL_LIBS ${CHR_SOURCES} ${CHR_SOURCES_GENERATED})
swipl_plugin(chr
	     PL_LIBS ${CMAKE_CURRENT_BINARY_DIR}/chr.pl)

swipl_examples(${CHR_EXAMPLES})

test_libs(chr)
