include $(top_srcdir)/config/Makefile.for.ROSE.includes.and.libs

ROSE_FLAGS = -rose:verbose 0 -I$(srcdir)

AM_CPPFLAGS = $(ROSE_INCLUDES) 
AM_LDFLAGS = $(ROSE_RPATHS)
LDADD    = $(ROSE_LIBS)

JOVIAL_TESTCODES = \
 tiny.jov                               \
 tiny_comments.jov                      \
 bit_conversion.jov                     \
 int_conversion.jov                     \
 item_desc_conversion.jov               \
 parens.jov                             \
 typename_conv.jov                      \
 status_enumval.jov                     \
 use_table_types.jov                    \
 1_2_2_non-nested-subroutine_a.jov      \
 1_2_2_non-nested-subroutine_b.jov      \
 1_2_2_procedure-module_a.jov           \
 1_2_2_procedure-module_b.jov           \
 1_2_2_procedure-module_e.jov           \
 1_2_2_procedure-module_f.jov           \
 1_2_3_main-program-module_a.jov        \
 1_2_3_main-program-module_b.jov        \
 1_2_3_main-program-module_c.jov        \
 1_2_3_main-program-module_d.jov        \
 1_2_3_program-body_a.jov               \
 1_2_3_program-body_b.jov               \
 1_2_3_program-body_c.jov               \
 2_1_1_4_bit_type.jov                   \
 2_1_1_6_status_item_b.jov              \
 2_1_1_7_pointer_type.jov               \
 2_1_2_simple_table_var.jov             \
 2_1_2_compound_table_var.jov           \
 2_1_2_1_table_dimension_list_a.jov     \
 2_1_2_1_table_dimension_list_b.jov     \
 2_1_2_2_structure_spec.jov             \
 2_1_2_3_packing_spec.jov               \
 2_1_3_constant_table_var.jov           \
 2_1_6_block_preset_list.jov            \
 2_4_define_j.jov                       \
 3_2_function_result.jov                \
 4_2_loop_stmt_b.jov                    \
 4_2_loop_stmt_b1.jov                   \
 4_2_loop_stmt_d.jov                    \
 4_2_loop_stmt_d1.jov                   \
 4_2_loop_stmt_while_a.jov              \
 4_2_loop_stmt_while_b.jov              \
 4_3_if_stmt_a.jov                      \
 4_3_if_stmt_b.jov                      \
 4_3_if_stmt_c.jov                      \
 4_3_if_stmt_d.jov                      \
 4_3_if_stmt_e.jov                      \
 4_4_case_stmt_a.jov                    \
 4_5_proc_call_stmt.jov                 \
 4_8_exit_stmt_a.jov                    \
 4_9_stop_stmt_a.jov                    \
 4_9_stop_stmt_b.jov                    \
 4_9_stop_stmt_c.jov                    \
 4_10_abort_stmt_a.jov                  \
 4_10_abort_stmt_b.jov                  \
 5_2_logical_continuation_a.jov         \
 5_2_logical_continuation_b.jov         \
 5_2_logical_continuation_amb.jov       \
 6_1_byte_function_variable.jov         \
 6_1_ptr_dereference.jov                \
 6_1_table_dereference.jov              \
 6_3_user_def_function_call.jov         \
 6_3_4_byte_function.jov                \
 6_3_5_shift_function.jov               \
 6_3_6_abs_function.jov                 \
 6_3_10_nwdsen_function.jov             \
 9_0_directives.jov                     \
 rose-issue-1507.jov                    \
 rose-issue-1516.jov                    \
 rose-issue-2100.jov                    \
 rose-issue-2143_j.jov                  \
 rose-issue-2775.jov                    \
 rose-issue-2776.jov                    \
 rose-issue-rc-2.jov                    \
 rose-issue-rc-19.jov                   \
 rose-issue-rc-41a.jov                  \
 rose-issue-rc-41b.jov                  \
 rose-issue-rc-42a.jov                  \
 rose-issue-rc-42b.jov                  \
 rose-issue-rc-42c.jov                  \
 rose-issue-rc-69.jov                   \
 rose-issue-rc-84.jov                   \
 rose-issue-rc-85.jov                   \
 rose-issue-rc-86.jov                   \
 rose-issue-rc-88.jov                   \
 rose-issue-rc-91.jov                   \
 rose-issue-rc-94.jov                   \
 rose-issue-rc-96.jov                   \
 rose-issue-rc-122-lcopy.jov            \
 rose-issue-rc-133.jov                  \
 rose-issue-rc-134.jov                  \
 rose-issue-rc-135.jov                  \
 rose-issue-rc-136.jov                  \
 rose-issue-rc-136a.jov                 \
 rose-issue-rc-137.jov                  \
 rose-issue-rc-138.jov                  \
 rose-issue-rc-139.jov                  \
 rose-issue-rc-144a.jov                 \
 rose-issue-rc-144b.jov                 \
 rose-issue-rc-155.jov                  \
 rose-issue-rc-156.jov                  \
 rose-issue-rc-157.jov                  \
 rose-issue-rc-158.jov                  \
 rose-issue-rc-159.jov                  \
 rose-issue-rc-160.jov                  \
 rc161.pre.jov                          \
 rose-issue-rc-179.jov                  \
 rose-issue-rc-186.jov                  \
 rose-issue-rc-189.jov                  \
 rose-issue-rc-190.jov                  \
 rose-issue-rc-191.jov                  \
 rose-issue-rc-192.jov                  \
 rose-issue-rc-193.jov                  \
 rose-issue-rc-201.jov                  \
 rose-issue-rc-201.pre.jov              \
 rose-issue-rc-203.jov                  \
 rose-issue-rc-203.pre.jov              \
 rose-issue-rc-204.jov                  \
 rose-issue-rc-225.jov                  \
 rose-issue-rc-225.pre.jov              \
 rose-issue-rc-227.jov                  \
 rose-issue-rc-240.jov                  \
 rose-issue-rc-241.jov                  \
 rose-issue-rc-260.jov                  \
 rose-issue-rc-271.jov                  \
 rose-issue-rc-271.pre.jov              \
 rose-issue-rc-290.jov                  \
 rose-issue-rc-290.pre.jov              \
 rose-issue-rc-291.jov                  \
 rose-issue-rc-333.jov                  \
 rose-issue-rc-333.pre.jov              \
 rose-issue-rc-334.jov                  \
 rose-issue-rc-334.pre.jov              \
 rose-issue-rc-336.jov                  \
 rose-issue-rc-336.pre.jov              \
 rose-issue-rc-337.jov                  \
 rose-issue-rc-337.pre.jov              \
 rose-issue-rc-338.jov                  \
 rose-issue-rc-338.pre.jov              \
 rose-issue-rc-339.jov                  \
 rose-issue-rc-341.jov                  \
 rose-issue-rc-341.pre.jov              \
 rose-issue-rc-360.jov                  \
 rose-issue-rc-360.pre.jov              \
 rose-issue-rc-365.jov                  \
 rose-issue-rc-383.jov                  \
 rose-issue-rc-390.jov                  \
 rose-issue-rc-390.pre.jov              \
 rose-issue-rc-391.jov                  \
 rose-issue-rc-391.pre.jov              \
 rose-issue-rc-392.jov                  \
 rose-issue-rc-392.pre.jov              \
 rose-issue-rc-394.jov                  \
 rose-issue-rc-394.pre.jov              \
 rose-issue-rc-400.jov                  \
 rose-issue-rc-400.pre.jov              \
 rose-issue-rc-410.jov                  \
 rose-issue-rc-410.pre.jov              \
 rose-issue-rc-413.jov                  \
 rose-issue-rc-413.pre.jov              \
 rose-issue-rc-416.jov                  \
 rose-issue-rc-416.pre.jov              \
 rose-issue-rc-429.jov                  \
 rose-issue-rc-429.pre.jov              \
 rose-issue-rc-448.jov                  \
 rose-issue-rc-448.pre.jov              \
 rose-issue-rc-449.jov                  \
 rose-issue-rc-449.pre.jov              \
 rose-issue-rc-457.jov                  \
 rose-issue-rc-457.pre.jov              \
 rose-issue-rc-459.jov                  \
 rose-issue-rc-461a.jov                 \
 rose-issue-rc-461b.jov                 \
 rose-issue-rc-470.jov                  \
 rose-issue-rc-472.jov                  \
 rose-issue-rc-473.jov                  \
 rose-issue-rc-503.jov                  \
 rose-issue-rc-523.jov                  \
 rose-issue-rc-575.jov                  \
 rose-issue-rc-578.jov                  \
 rose-issue-rc-581.jov                  \
 rose-issue-rc-596.jov                  \
 rose-issue-rc-638a.jov                 \
 rose-issue-rc-642.jov                  \
 rose-issue-rc-646.jov                  \
 rose-issue-rc-647.jov                  \
 rose-issue-rc-648.jov                  \
 rose-issue-rc-649.jov                  \
 rose-issue-rc-650.jov                  \
 rose-issue-rc-651.jov                  \
 rose-issue-rc-652.jov                  \
 rose-issue-rc-670.jov                  \
 rose-issue-rc-674.jov                  \
 rose-issue-rc-687.jov                  \
 rose-issue-rc-692.jov                  \
 rose-issue-rc-693.jov                  \
 rose-issue-rc-715.jov                  \
 rose-issue-rc-753a.jov                 \
 rose-issue-rc-753b.jov                 \
 rose-issue-rc-754.jov                  \
 rose-issue-rc-755.jov                  \
 rose-issue-rc-763.jov                  \
 rose-issue-rc-765.jov                  \
 rose-issue-rc-787.jov                  \
 rose-issue-rc-789.jov                  \
 rose-issue-rc-793.jov                  \
 rose-issue-rc-797.jov                  \
 rose-issue-rc-802.jov                  \
 rose-issue-rc-803.jov                  \
 rose-issue-rc-813.jov                  \
 rose-issue-rc-818.jov                  \
 rose-issue-rc-819.jov                  \
 rose-issue-rc-820.jov                  \
 rose-issue-rc-821.jov                  \
 rose-issue-rc-822.jov                  \
 rose-issue-rc-823.jov                  \
 rose-issue-rc-824.jov                  \
 rose-issue-rc-825.jov                  \
 rose-issue-rc-826.jov                  \
 rose-issue-rc-836.jov                  \
 rose-issue-rc-975.jov                  \
 gitlab-issue-12.jov                    \
 gitlab-issue-13.jov                    \
 gitlab-issue-41.jov                    \
 gitlab-issue-84.jov                    \
 gitlab-issue-162.jov                   \
 gitlab-issue-181.jov                   \
 gitlab-issue-182.jov                   \
 gitlab-issue-186.jov                   \
 charlie.jov                            \
 shadow.jov                             \
 comments.jov                           \
 comments_assign.jov                    \
 comments_loop.jov                      \
 comments_start_term.jov                \
 comments_start_term_procmod.jov

JOVIAL_PARSER_TESTCODES = \
 fixed_cast.jov                         \
 tables_and_pointers.jov                \
 2_1_1_5_char_item_desc.jov             \
 4_3_if_else_stmt.jov                   \
 4_6_return_stmt_a.jov                  \
 4_7_goto_stmt_a.jov                    \
 5_1_1_integer-precedence.jov           \
 5_1_1_integer-primary.jov              \
 5_1_1_integer-term.jov                 \
 5_2_1_relational_expressions_a.jov     \
 6_3_2_next_function_pointer.jov        \
 6_3_2_next_function_status.jov

## List compool modules that need to be compiled first:
#     rc161b.pre.cpl before rc161a.pre.cpl before rc161.jov
#
COMPOOL_TESTCODES = \
 alpha.cpl                              \
 define_dollar.cpl                      \
 multi.cpl                              \
 rectype.cpl                            \
 simple_compool.cpl                     \
 status_type.cpl                        \
 table_inheritance.cpl                  \
 table_names.cpl                        \
 table_types.cpl                        \
 tighttable.cpl                         \
 2_4_define.cpl                         \
 3_0_rent_and_rec.cpl                   \
 rc161b.pre.cpl                         \
 rc600a.cpl                             \
 rc616b.cpl                             \
 rc687a.cpl                             \
 rc715a.cpl                             \
 rc833.cpl                              \
 rose-issue-2143.cpl                    \
 rose-issue-2267.cpl                    \
 rose-issue-2654.cpl                    \
 rose-issue-2658.cpl                    \
 rose-issue-2683.cpl                    \
 rose-issue-2687.cpl                    \
 rose-issue-2690.cpl                    \
 rose-issue-2691.cpl                    \
 rose-issue-2698.cpl                    \
 rose-issue-2701.cpl                    \
 rose-issue-2702.cpl                    \
 rose-issue-2766.cpl                    \
 rose-issue-2777.cpl                    \
 rose-issue-rc-6.cpl                    \
 rose-issue-rc-7.cpl                    \
 rose-issue-rc-9.cpl                    \
 rose-issue-rc-11.cpl                   \
 rose-issue-rc-12.cpl                   \
 rose-issue-rc-14.cpl                   \
 rose-issue-rc-15.cpl                   \
 rose-issue-rc-16.cpl                   \
 rose-issue-rc-49.cpl                   \
 rose-issue-rc-50.cpl                   \
 rose-issue-rc-51.cpl                   \
 rose-issue-rc-52.cpl                   \
 rose-issue-rc-53.cpl                   \
 rose-issue-rc-55.cpl                   \
 rose-issue-rc-55a.cpl                  \
 rose-issue-rc-56.cpl                   \
 rose-issue-rc-79a.cpl                  \
 rose-issue-rc-87.cpl                   \
 rose-issue-rc-92a.cpl                  \
 rose-issue-rc-93.cpl                   \
 rose-issue-rc-95.cpl                   \
 rose-issue-rc-118.cpl                  \
 rose-issue-rc-119a.cpl                 \
 rose-issue-rc-120.cpl                  \
 rose-issue-rc-121.cpl                  \
 rose-issue-rc-128.cpl                  \
 rose-issue-rc-129.cpl                  \
 rose-issue-rc-160a.cpl                 \
 rose-issue-rc-461.cpl                  \
 rose-issue-rc-512.cpl                  \
 rose-issue-rc-531.cpl                  \
 rose-issue-rc-587.cpl                  \
 rose-issue-rc-600.cpl                  \
 rose-issue-rc-642.cpl                  \
 rose-issue-rc-645.cpl                  \
 rose-issue-rc-676.cpl                  \
 rose-issue-rc-677.cpl                  \
 rose-issue-rc-737.cpl                  \
 rose-issue-rc-741.cpl                  \
 rose-issue-rc-742.cpl                  \
 rose-issue-rc-745.cpl                  \
 rose-issue-rc-746.cpl                  \
 rose-issue-rc-766.cpl                  \
 rose-issue-rc-786.cpl                  \
 rose-issue-rc-833.cpl                  \
 rose-issue-rc-839.cpl                  \
 rose-issue-rc-967.cpl                  \
 rose-issue-rc-968.cpl                  \
 rose-issue-rc-969.cpl                  \
 rose-issue-rc-998.cpl                  \
 rose-issue-rc-999.cpl                  \
 rc161a.pre.cpl                         \
 rc410.cpl                              \
 rc410.pre.cpl                          \
 rc503.cpl                              \
 rc515.cpl                              \
 rc596.cpl                              \
 rc616a.cpl                             \
 rc687b.cpl                             \
 rc715b.cpl                             \
 rc754.cpl                              \
 rc802.cpl                              \
 rc820.cpl                              \
 rc821.cpl                              \
 rc825.cpl                              \
 rc836.cpl                              \
 rc975.cpl                              \
 gitlab-issue-12.cpl                    \
 gitlab-issue-14.cpl                    \
 gitlab-issue-17.cpl                    \
 gitlab-issue-74.cpl                    \
 beta.cpl                               \
 parttype.cpl                           \
 comments_start_term.cpl

COMPOOL_DIRECTIVE_TESTCODES = \
 9_1_compool_directive.cpl              \
 rose-issue-rc-79b.cpl                  \
 rose-issue-rc-92b.cpl                  \
 rose-issue-rc-119b.cpl                 \
 rose-issue-rc-515.cpl                  \
 rose-issue-rc-616.cpl

# proc_refs.cpl                          


COMPOOL_PARSER_TESTCODES = \
 constant_item_presets.cpl              \
 item_and_status_type_J.cpl             \
 simple_def_ambiguity_J.cpl             \
 size_function_J.cpl                    \
 spec_table_decl_ambiguity_J.cpl        \
 spec_table_options_null_J.cpl          \
 table_and_status_type_J.cpl            \
 table_preset_J.cpl                     \
 table_ref_formula_ambiguity_J.jov      \
 2_2_compound_block_type.cpl            \
 2_2_compound_table_type.cpl            \
 2_2_simple_block_type.cpl              \
 2_2_simple_table_type.cpl              \
 2_5_def_ref_item.cpl                   \
 5_1_fixed_or_float.cpl                 \
 rose-issue-1518.cpl                    \
 rose-issue-1520.cpl                    \
 rose-issue-2286.cpl

# should finish formulas next
#
JOVIAL_TESTCODES_PASS_TRAVERSE = \
 4_0_compound_stmt_a.jov                \
 4_0_compound_stmt_b.jov                \
 4_0_null_block_stmt.jov                \
 4_3_if_stmt_d.jov                      \
 4_3_if_stmt_e.jov                      \
 4_7_goto_stmt_b.jov                    \
 5_3_character_formula_a.jov            \
 5_3_character_formula_b.jov            \
 5_3_character_formula_c.jov            \
 5_3_character_formula_d.jov            \
 5_4_status_formula_a.jov               \
 5_4_status_formula_b.jov               \
 5_4_status_formula_c.jov               \
 5_4_status_formula_d.jov               \
 5_5_pointer_formula_a.jov              \
 5_5_pointer_formula_b.jov              \
 5_5_pointer_formula_c.jov              \
 5_5_pointer_formula_d.jov              \
 table_type.cpl                         \
 rose-issue-2144.cpl

JOVIAL_TESTCODES_WORKING_ON = \
 rose-issue-2101.jov                    \
 rose-issue-2102.jov                    \
 rose-issue-2104.jov                    \
 rose-issue-2105.jov                    \
 rose-issue-2106.jov                    \
 rose-issue-2107.jov                    \
 rose-issue-2145.jov                    \
 rose-issue-2146.jov                    \
 rose-issue-2147.jov                    \
 rose-issue-2148.jov                    \
 rose-issue-2149.jov                    \
 rose-issue-2150.jov                    \
 1_2_2_procedure_module_c.jov           \
 1_2_2_procedure_module_d.jov           \
 1_2_2_procedure_module_g.jov           \
 1_2_3_program-body_d.jov               \
 1_2_3_program-body_e.jov               \
 1_2_3_program-body_f.jov               \
 1_2_3_program-body_g.jov               \
 1_2_3_program-body_h.jov               \
 4_1_assignment_stmt_a.jov              \
 4_1_assignment_stmt_b.jov              \
 4_2_loop_stmt_c.jov                    \
 4_6_return_stmt_b.jov                  \
 4_10_abort_stmt_c.jov                  \
 5_1_1_integer-factor.jov               \
 5_1_1_integer-formula.jov

## TODO: Don't seem to be able to run just parser tests
#  - but don't really need to anymore as we've moved beyond just parsing
#
TEST_JOVIAL_PARSER_Objects  = ${JOVIAL_PARSER_TESTCODES:.jov=.aterm}
TEST_JOVIAL_PARSER_Sources  = ${JOVIAL_PARSER_TESTCODES:.jov=.jov.passed}

TEST_COMPOOL_PARSER_Objects = ${COMPOOL_PARSER_TESTCODES:.cpl=.aterm}
TEST_COMPOOL_PARSER_Sources = ${COMPOOL_PARSER_TESTCODES:.cpl=.cpl.passed}

TEST_JOVIAL_Objects  = ${JOVIAL_TESTCODES:.jov=.aterm}
TEST_JOVIAL_Sources  = ${JOVIAL_TESTCODES:.jov=.jov.passed}

TEST_COMPOOL_Objects = ${COMPOOL_TESTCODES:.cpl=.aterm}
TEST_COMPOOL_Sources = ${COMPOOL_TESTCODES:.cpl=.cpl.passed}

TEST_DIRECTIVE_Objects = ${COMPOOL_DIRECTIVE_TESTCODES:.cpl=.aterm}
TEST_COMPOOL_Sources = ${COMPOOL_DIRECTIVE_TESTCODES:.cpl=.cpl.passed}

PASSING_TEST_Objects = $(TEST_COMPOOL_Objects) $(TEST_JOVIAL_Objects) $(TEST_DIRECTIVE_Objects)
PASSING_COMPOOL_TEST_Objects = $(TEST_COMPOOL_Objects)

# Go back and build the translators we are using to test Jovial (in case make check
# is run directly in this directory before make has been run from the root of the 
# ROSE directory structure).
#../../testParser:
#	cd ../..; $(MAKE) testParser
../../testTranslator:
	cd ../..; $(MAKE) testTranslator

$(TEST_JOVIAL_PARSER_Objects): ../../testParser
	../../testParser $(ROSE_FLAGS) -rose:jovial $(srcdir)/$(@:.aterm=.jov)

$(TEST_COMPOOL_PARSER_Objects): ../../testParser
	../../testParser $(ROSE_FLAGS) -rose:jovial $(srcdir)/$(@:.aterm=.cpl)

$(TEST_JOVIAL_Objects): ../../testTranslator
	../../testTranslator -rose:jovial $(srcdir)/$(@:.aterm=.jov)

$(TEST_COMPOOL_Objects): ../../testTranslator
	../../testTranslator -rose:jovial $(srcdir)/$(@:.aterm=.cpl)

$(TEST_DIRECTIVE_Objects): ../../testTranslator
	../../testTranslator -rose:jovial $(srcdir)/$(@:.aterm=.cpl)

check-compool:
	@echo $(TEST_COMPOOL_Objects)
	@echo $(PASSING_TEST_COMPOOL_Objects)
check-jovial:
	@echo "TEST_JOVIAL_Objects:"
	@echo $(TEST_JOVIAL_Objects)
	@echo "PASSING_TEST_Objects:"
	@echo $(PASSING_TEST_Objects)

clean-local:
	rm -f rose_*.* *.aterm *.rcmp *.dot

check-local:
	@echo "Tests for experimental Jovial frontend."
	@$(MAKE) $(PASSING_TEST_Objects)
	@echo "***********************************************************************************************************************"
	@echo "****** ROSE/tests/nonsmoke/functional/CompileTests/experimental_jovial_tests: make check terminated successfully ******"
	@echo "***********************************************************************************************************************"
