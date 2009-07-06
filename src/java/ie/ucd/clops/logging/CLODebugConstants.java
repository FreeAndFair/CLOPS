package ie.ucd.clops.logging;

import mobius.logging.DefaultDebugConstants;

/**
 * The <code>CLODebugConstants</code> interface collects together all constants relating
 * to logging and debugging in the CLOPS system.
 *
 * To add a new statistic or category to CLOPS simply add it to the appropriate
 * list below, add the appropriate field(s) below, and being using it in your
 * subsystem.
 *
 * @design We reuse the default categories, levels, and messages
 * found in {@link DefaultDebugConstants}.
 *
 * @author kiniry
 *
 */
public class CLODebugConstants extends DefaultDebugConstants {
  /**
   * The following categories, which initially mimic the subsystems of
   * CLOPS, are logged by the CLOPS logging subsystem:
   * <ul>
   * <li>CODEGEN</li> Events relating to code generation.
   * <li>DOCUMENTATION</li> Events relating to documentation generation.
   * <li>DSL</li> General events relating to the CLOPS DSL.
   * <li>DSL_PARSER</li> Events relating to the CLOPS DSL parser.
   * <li>DSL_STRUCTS</li> Events relating to the CLOPS DSL data-structures.
   * <li>RUNTIME</li> General runtime-related events.
   * <li>RUNTIME_AUTOMATON</li> Events specific to automaton construction.
   * <li>RUNTIME_FLYRULES</li> Events specific to flyrule generation.
   * <li>RUNTIME_OPTIONS</li> Events specific to option processing.
   * <li>RUNTIME_PARSER</li> Events specific to runtime parsing of command lines.
   * </ul>
   */
  static final String
  CODEGEN = "CODEGEN",
  DOCUMENTATION = "DOCS",
  DSL = "DSL",
  DSL_PARSER = "DSL_PARSER",
  DSL_STRUCTS = "STRUCTS",
  RUNTIME = "RT",
  RUNTIME_AUTOMATON = "AUTO",
  RUNTIME_FLYRULES = "FLY",
  RUNTIME_OPTIONS = "OPT",
  RUNTIME_PARSER = "RT_PARSER";

  /**
   * The following statistics are gathered by the CLOPS logging subsystem.  Unless
   * otherwise noted, all are stated with respect to a given CLOPS DSL input specification.
   * <ul>
   * <li>ARGUMENT_SIZE</li> The number of arguments in the command line under analysis.
   * <li>AUTOMATON_SIZE</li> The number of states in a generated automaton.
   *
   * <li>OPTION_PROCESSING_TIME</li> A pair consisting of (1) the size of a
   * command line and (2) number of milliseconds needed to process it.
   * <li>DSL_PROCESSING_TIME</li> A triple consisting of (1) the name of a CLOPS
   * specification, (2) the size of that spec, and (3) the number of milliseconds
   * needed to processes it.
   *
   * <li>DSL_ARGS_COUNT</li> The number of arguments in an ARGS section.
   * <li>DSL_PROPERTY_COUNT</li> The number of properties in an ARGS section.
   * <li>DSL_ARGS_PER_PROPERTY</li> The number of arguments related to a single property.
   *
   * <li>DSL_COMMENT_COUNT</li> The number of comments provided.
   *
   * <li>DSL_ARGS_FORMAT_SIZE</li> The size (number of subclauses) of the FORMAT section.
   *
   * <li>DSL_WHERE_COUNT</li> The number of WHERE clauses used.
   * <li>DSL_WHERE_SIZE</li> The number of children in a WHERE clause.
   *
   * <li>DSL_FLY_COUNT</li> The number of FLY rules used in a CLOPS DSL spec.
   * <li>DSL_FLY_SIZE</li> The number of assignments in a FLY rule.
   *
   * <li>DSL_OVERRIDES_COUNT</li> The number of OVERRIDES.
   *
   * <li>DSL_VALIDITY_COUNT</li> The number of VALIDITY rules.
   *
   * <li>DSL_CONSTANT_COUNT</li> The number of constants used in a CLOPS DSL spec.
   * <li>DSL_POPULAR_CONSTANTS</li> A ordered list of pairs, each of which contains
   * (1) a constant value, and (2) the frequency with which the constant value is used.
   * The list is ordered in a decreasing fashion with respect to component (2).
   *
   * <li>DSL_SPEC_SIZE</li> The overall size of a CLOPS DSL specification.  Size is defined
   * as the sum of the sizes of ARGS_COUNT, DSL_ARGS_FORMAT_SIZE, DSL_WHERE_COUNT,
   * DSL_FLY_COUNT, DSL_OVERRIDES_COUNT, and DSL_VALIDITY_COUNT.
   * <li>CLO_SPEC_COMPLEXITY</li> The overall complexity of the command line specified
   * by a given CLOPS DSL specification.  Complexity is defined as the sum of all
   * values generated for the following statistics for a given CLOPS DSL spec:
   * DSL_PROPERTY_COUNT, DSL_WHERE_COUNT, DSL_FLY_SIZE, DSL_OVERRIDES_COUNT,
   * DSL_VALIDITY_COUNT, DSL_CONSTANT_COUNT.
   *
   * <li>CODE_GEN_SIZE</li> The size, in LOC, of the generated code.
   * </ul>
   */
  static final String
  ARGUMENT_SIZE = "ARG_SIZE",
  AUTOMATON_SIZE = "AUTO_SIZE",
  OPTION_PROCESSING_TIME = "OPT_PROC_TIME",
  DSL_PROCESSING_TIME = "DSL_PROC_TIME",
  DSL_ARGS_COUNT = "ARGS_COUNT",
  DSL_PROPERTY_COUNT = "PROP_COUNT",
  DSL_ARGS_PER_PROPERTY = "ARGS_PER_PROP",
  DSL_COMMENT_COUNT = "COMMENT_COUNT",
  DSL_ARGS_FORMAT_SIZE = "FORMAT_SIZE",
  DSL_WHERE_COUNT = "WHERE_COUNT",
  DSL_WHERE_SIZE = "WHERE_SIZE",
  DSL_FLY_COUNT = "FLY_COUNT",
  DSL_FLY_SIZE = "FLY_SIZE",
  DSL_OVERRIDES_COUNT = "OVERRIDES_COUNT",
  DSL_VALIDITY_COUNT = "VALIDITY_COUNT",
  DSL_CONSTANTS_COUNT = "CONSTANTS_COUNT",
  DSL_POPULAR_CONSTANTS = "POPULAR_CONSTANTS",
  DSL_SPEC_SIZE = "SPEC_SIZE",
  CLO_SPEC_COMPLEXITY = "SPEC_COMPLEXITY",
  CODE_GEN_SIZE = "CODE_GEN_SIZE";
}
