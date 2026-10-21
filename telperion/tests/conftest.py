"""Test configuration for the public copy of Telperion.

The test suite comes from the development repository, where it runs against that repository's full
contents: example projects, the missions registry, repository-level scripts and CI workflow files, and
Lean projects. Only the engine and a selection of examples are published here, so a small part of the
suite cannot run in this copy. Twelve test modules that cannot even be imported without those files are
left out of this copy; the tests below are skipped, each with its reason; everything else runs as in
development. (In the published copy: 105 individual tests skipped, out of about 3,000 tests.)
"""
import pytest

#: Individual tests that need a file, script or Lean project from the development repository.
_NEEDS_DEVELOPMENT_REPOSITORY = {
    "tests/rh_jensen/test_end_to_end_d2.py::test_check_mode_passes",
    "tests/rh_jensen/test_end_to_end_d2.py::test_generate_writes_lean_no_sorry",
    "tests/rh_jensen/test_end_to_end_d2.py::test_generated_lean_builds_green",
    "tests/rh_jensen/test_end_to_end_d2.py::test_generated_lean_contains_axle_gate",
    "tests/rh_jensen/test_end_to_end_d2.py::test_generated_lean_contains_theorem",
    "tests/rh_jensen/test_grid.py::test_grid_mode_all_theorems_have_roots_card_2",
    "tests/rh_jensen/test_grid.py::test_grid_mode_axle_gates_present",
    "tests/rh_jensen/test_grid.py::test_grid_mode_exits_zero",
    "tests/rh_jensen/test_grid.py::test_grid_mode_no_sorry",
    "tests/rh_jensen/test_grid.py::test_grid_mode_print_axioms_lines",
    "tests/rh_jensen/test_grid.py::test_grid_mode_writes_three_theorems",
    "tests/rh_jensen/test_grid.py::test_n_list_mode_subset",
    "tests/test_armrate_family.py::test_certifies_full_range_peak_five_and_straddles_one",
    "tests/test_armrate_family.py::test_emit_is_lint_clean_and_idempotent",
    "tests/test_armrate_family.py::test_false_bound_would_be_refused",
    "tests/test_armrate_family.py::test_ratio_matches_armrate_closed_form_and_nearstar",
    "tests/test_bg_family.py::test_generated_example_has_heartbeat_budget_and_is_idempotent",
    "tests/test_bg_floor.py::test_generated_example_is_idempotent_with_heartbeat_budget",
    "tests/test_bg_floor_families.py::test_class_taxonomy_and_names",
    "tests/test_bg_floor_families.py::test_emit_is_lint_clean_and_search_free",
    "tests/test_bg_floor_families.py::test_every_family_cell_bernstein_certifies",
    "tests/test_bg_floor_families.py::test_generated_example_is_idempotent_with_heartbeat_budgets",
    "tests/test_bg_floor_families.py::test_rational_brackets_are_valid",
    "tests/test_bg_floor_families.py::test_too_high_a_floor_is_refused",
    "tests/test_bragg_floor_emitter.py::test_frozen_output_matches_regeneration",
    "tests/test_bragg_floor_emitter.py::test_generated_ladder_emits_cleared_rungs_and_atom",
    "tests/test_ci_axiom_gate.py::test_workflows_carry_the_expected_number_of_axiom_gates",
    "tests/test_dvp_box.py::test_all_zeros_up_to_height_100_builds",
    "tests/test_dvp_box.py::test_all_zeros_up_to_height_builds",
    "tests/test_dvp_box.py::test_axiom_guard_rh_in_box_bites",
    "tests/test_dvp_box.py::test_wide_box_winding_agrees_29",
    "tests/test_dvp_box.py::test_zeta_confinement_builds",
    "tests/test_emit_baez_duarte.py::test_generated_example_decreasing_sequence",
    "tests/test_emit_bagchi_recurrence.py::test_generated_example_builds",
    "tests/test_emit_complex_re_im_split.py::test_cast_site_gates_restate_the_island_verbatim",
    "tests/test_emit_complex_re_im_split.py::test_dogfood_consumer_gates_retire_the_e6bridge7_hand_haves",
    "tests/test_emit_complex_re_im_split.py::test_dogfood_regenerates_byte_for_byte",
    "tests/test_emit_complex_re_im_split.py::test_gauss_haves_are_reproduced_from_e6bridge7",
    "tests/test_emit_complex_re_im_split.py::test_li_face_statements_are_byte_identical_to_the_hand_lemmas",
    "tests/test_emit_exp_enclosure.py::test_reads_bragg_defect_literals_verbatim",
    "tests/test_emit_exp_threshold.py::test_dogfood_file_is_regenerable_byte_for_byte",
    "tests/test_emit_exp_threshold.py::test_dogfood_file_regenerates_the_two_sites_under_new_names",
    "tests/test_emit_exp_threshold.py::test_e6bridge7_skeleton_lines_are_verbatim_island_lines",
    "tests/test_emit_exp_threshold.py::test_emit_e6bridge14_log_step_is_the_island_lemma_verbatim",
    "tests/test_emit_exp_threshold.py::test_product_atom_lines_are_verbatim_island_lines",
    "tests/test_emit_interval_gram_inertia.py::test_example_generate_check_is_clean",
    "tests/test_emit_interval_gram_inertia.py::test_example_lean_is_axiom_guarded_and_sorry_free",
    "tests/test_emit_lehmer_pair.py::test_generated_example_builds",
    "tests/test_emit_robin_growth.py::test_generated_example_builds_rungs",
    "tests/test_emit_twofreq_offline.py::test_statement_matches_mm_node",
    "tests/test_emit_zero_sum_majorant.py::test_dogfood_file_is_regenerable_byte_for_byte",
    "tests/test_emit_zero_sum_majorant.py::test_dogfood_regenerates_the_three_sites_under_new_names",
    "tests/test_emit_zero_sum_majorant.py::test_emitted_gamma_rewrite_is_the_prelude_line_verbatim",
    "tests/test_judge_log.py::test_kernel_modes_cover_what_the_workflow_can_print",
    "tests/test_li_positivity.py::test_bundle_face_packages_the_same_literals_once",
    "tests/test_li_positivity.py::test_generated_ladder_has_twenty_rungs_and_refutation_atom",
    "tests/test_missions_bg_ceiling_constant.py::test_ceiling_literal_equals_dns_peak",
    "tests/test_missions_campaigns.py::test_campaigns_are_discovered",
    "tests/test_missions_judge.py::test_a_heavy_node_does_not_poison_the_nodes_after_it",
    "tests/test_missions_judge.py::test_artifact_context_collects_namespace_and_opens",
    "tests/test_missions_judge.py::test_artifact_in_subdirectory_gets_dotted_solution_module",
    "tests/test_missions_judge.py::test_binderless_statement_has_no_forall",
    "tests/test_missions_judge.py::test_bridge_module_has_registered_type_and_artifact_proof",
    "tests/test_missions_judge.py::test_bundle_files_and_check",
    "tests/test_missions_judge.py::test_cli_list_configs_check_and_write",
    "tests/test_missions_judge.py::test_configs_stdout_is_machine_readable_even_with_skipped_nodes",
    "tests/test_missions_judge.py::test_heavy_certificates_turns_nanoda_off_for_that_node_only",
    "tests/test_missions_judge.py::test_in_tree_island_keeps_examples_require_path",
    "tests/test_missions_judge.py::test_nanoda_off_when_requested",
    "tests/test_missions_judge.py::test_only_proved_nodes_are_judged",
    "tests/test_missions_judge.py::test_out_of_tree_island_bundle",
    "tests/test_missions_judge.py::test_split_signature_handles_colons_in_binders_and_ascriptions",
    "tests/test_missions_judge.py::test_split_signature_keeps_let_assignments_inside_the_conclusion",
    "tests/test_missions_judge.py::test_split_signature_refuses_extra_declarations",
    "tests/test_missions_judge.py::test_statement_name_not_suffix_of_theorem_is_refused",
    "tests/test_missions_judge.py::test_unconsumable_node_is_reported_not_fatal",
    "tests/test_missions_verify.py::test_disabled_step_does_not_vouch_for_an_island",
    "tests/test_rhinbox.py::test_driver_box_flag_emits_instantiation",
    "tests/test_rhinbox.py::test_driver_emitted_box_builds_sorry_free",
    "tests/test_rhinbox.py::test_driver_refuses_box_containing_pole",
    "tests/test_rhinbox.py::test_height_100_milestone_builds_sorry_free",
    "tests/test_rhinbox.py::test_height_100_winding_equals_online",
    "tests/test_rhinbox.py::test_rh_in_box_analytic_builds",
    "tests/test_rhinbox.py::test_rh_in_box_core_builds",
    "tests/test_rhinbox.py::test_rh_in_box_generic_and_regression_build",
    "tests/test_winding_count.py::test_winding_count_lean_no_drift",
    "tests/test_zeroloc_end_to_end.py::test_box_arg_principle_lambda_builds",
    "tests/test_zeroloc_end_to_end.py::test_zeta_blaschke_split_box_builds",
    "tests/test_zzl_legacy_split.py::test_aux_lakefile_default_name_unchanged",
    "tests/test_zzl_legacy_split.py::test_legacy_lakefile_is_a_named_package_with_its_targets",
    "tests/test_zzl_legacy_split.py::test_split_keeps_consumed_boxes_and_moves_the_rest",
}


def pytest_collection_modifyitems(config, items):
    skip = pytest.mark.skip(reason="needs a file, script or Lean project from the development repository, "
                                   "which is not included in this public copy")
    for item in items:
        if item.nodeid in _NEEDS_DEVELOPMENT_REPOSITORY:
            item.add_marker(skip)
