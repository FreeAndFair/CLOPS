package ie.ucd.clops.codegeneration;

import ie.ucd.clops.codegeneration.GeneratedCodeUnit.Visibility;
import ie.ucd.clops.dsl.OptionType;
import ie.ucd.clops.dsl.structs.AssignmentDescription;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.dsl.structs.FlyRuleDescription;
import ie.ucd.clops.dsl.structs.OptionDescription;
import ie.ucd.clops.dsl.structs.OptionGroupDescription;
import ie.ucd.clops.dsl.structs.OverrideRuleDescription;
import ie.ucd.clops.dsl.structs.Pair;
import ie.ucd.clops.dsl.structs.ValidityRuleDescription;
import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.options.CLOPSErrorOption;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.List;
import java.util.logging.Level;

/**
 * A class used to generate java code from a DSL.
 * @author Fintan
 * @author Mikolas Janota
 */
public class CodeGenerator {

  /** Put quotes around the given String */
  public static String quoteSimpleString(String s) {
    return "\"" + s + "\"";
  }

  /** Produces java String constant containing a given String that may contain newlines.*/
  public static String quoteMultilineString(String s) {
    String[] lines = s.split("\n");
    String retv = null;
    for (String line : lines) {
      line = line.trim();
      if (line.isEmpty()) continue;
      if (retv == null) retv = "";
      else retv  += "+ \n     ";
      retv += quoteSimpleString(line);
    }
    if (retv == null || retv.isEmpty()) retv = quoteSimpleString("");
    return retv;
  }

  public static void createCode(DSLInformation dslInfo, File outputDir, boolean genTest) {

    String parserName = dslInfo.getParserName();
    String formatString = dslInfo.getFormatString();
    Collection<OptionDescription> opDescriptions = dslInfo.getOptionDescriptions();
    Collection<OptionGroupDescription> opGroupDescriptions = dslInfo.getOptionGroupDescriptions();
    Collection<FlyRuleDescription> overrideRuleDescriptions = dslInfo.getFlyRuleDescriptions();

    //Specific parser
    GeneratedClassOrInterface specificParser = createSpecificParser(parserName, formatString, opDescriptions, opGroupDescriptions, overrideRuleDescriptions, dslInfo.getPackageName());

    //OptionsInterface
    GeneratedClassOrInterface optionsInterface = createOptionsInterface(parserName, opDescriptions, dslInfo.getPackageName());

    //SpecificOptionsStore
    GeneratedClassOrInterface specificOptionStore = createSpecificOptionStore(parserName, opDescriptions, opGroupDescriptions, dslInfo.getPackageName());

    //SpecificRuleStore
    GeneratedClassOrInterface specificRuleStore = createSpecificRuleStore(parserName, dslInfo, dslInfo.getPackageName());

    try {
      writeGeneratedClasses(outputDir, specificParser, optionsInterface, specificOptionStore, specificRuleStore);
      if (genTest) {
        GeneratedClassOrInterface tester = createTester(parserName, dslInfo.getPackageName());
        writeGeneratedClass(outputDir, tester);
      }
    } catch (FileNotFoundException fnfe) {
      fnfe.printStackTrace();
      CLOLogger.getLogger().log(Level.SEVERE, "Error creating file. " + fnfe);
    }

  }

  private static void writeGeneratedClasses(File outputDir, GeneratedClassOrInterface... classes) throws FileNotFoundException {
    for (GeneratedClassOrInterface genClass : classes) {
      writeGeneratedClass(outputDir, genClass);
    }
  }

  private static void writeGeneratedClass(File outputDir, GeneratedClassOrInterface... genClasses) throws FileNotFoundException {
    for (GeneratedClassOrInterface genClass : genClasses) {
      PrintWriter pw = new PrintWriter(new FileOutputStream(outputDir.getAbsolutePath() + File.separator + genClass.getName() + ".java"));
      new GeneratedCodePrinter(pw).printClass(genClass);
      pw.flush();
      pw.close();
    }
  }

  private static GeneratedMethod createOptionInitialisationMethod(
      String parserName,
      String packageName,
      GeneratedClassOrInterface specificParser, 
      Collection<OptionDescription> opDescriptions, 
      Collection<OptionGroupDescription> opGroupDescriptions) {

    GeneratedMethod createOps = new GeneratedMethod("createOptionStore", getQualifiedClassName(parserName + "OptionStore", packageName), Visibility.Private);
    createOps.addException("ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException");
    createOps.addStatement("return new " + parserName + "OptionStore()");
    return createOps;
  }

  private static void createRuleInitialisationCode(GeneratedClassOrInterface specificParser, String parserName) {
    GeneratedMethod createRules = new GeneratedMethod("createRuleStore", "ie.ucd.clops.runtime.rules.RuleStore", Visibility.Private);
    specificParser.addMethod(createRules);
    createRules.addStatement("return new " + parserName + "RuleStore()");    
  }

  private static GeneratedClassOrInterface createSpecificRuleStore(String parserName, DSLInformation dslInfo, String packageName) {
    List<FlyRuleDescription> flyRuleDescriptions = dslInfo.getFlyRuleDescriptions();

    GeneratedClassOrInterface ruleStore = new GeneratedClassOrInterface(parserName + "RuleStore", false, packageName, Visibility.Public);
    ruleStore.setSuperClass("ie.ucd.clops.runtime.rules.RuleStore");
    ruleStore.addImport("ie.ucd.clops.runtime.rules.Action");
    ruleStore.addImport("ie.ucd.clops.runtime.rules.Expression");
    ruleStore.addImport("ie.ucd.clops.runtime.rules.FlyRule");
    ruleStore.addImport("ie.ucd.clops.runtime.rules.OverrideRule");
    ruleStore.addImport("ie.ucd.clops.runtime.rules.Rule");
    ruleStore.addImport("ie.ucd.clops.runtime.rules.ValidityRule");


    GeneratedMethod constructor = new GeneratedConstructor(parserName + "RuleStore");
    ruleStore.addMethod(constructor);

    for (FlyRuleDescription flyRuleDescription : flyRuleDescriptions) {
      String opId = flyRuleDescription.getTriggeringOptionIdentifier();
      OptionDescription triggerOpDescription = dslInfo.getOptionDescriptionForIdentifier(opId);
      if (triggerOpDescription == null) {
        System.out.println("Error, option " + opId + " not found for fly rule");
      } else {
        String id = getUniqueID();
        String ruleName = "rule" + id;
        String conditionName = "rule" + id + "Condition"; 

        String conditionText = flyRuleDescription.getConditionText();
        if (conditionText == null || conditionText.equals("")) {
          constructor.addStatement("Rule " + ruleName + " = new FlyRule(\"" + opId + "\", Expression.TRUE)");
        } else {
          String conditionTypeName = "Rule" + id + "Condition";
          constructor.addStatement("Expression<Boolean> " + conditionName + " = new " + conditionTypeName + "()");
          ruleStore.addContainedClass(createSpecificExpression(conditionTypeName, "Boolean", conditionText));
          constructor.addStatement("Rule " + ruleName + " = new FlyRule(\"" + opId + "\", " + conditionName + ")");
        }


        int count = 1;
        for (AssignmentDescription desc : flyRuleDescription.getAssignments()) {
          OptionDescription lhsOpDescription = dslInfo.getOptionDescriptionForIdentifier(desc.getOptionIdentifier());
          if (lhsOpDescription == null) {
            System.out.println("Error, option " + desc.getOptionIdentifier() + " not found for assignment in fly rule");
          } else {
            String expressionName = "Rule" + id + "Expression" + (count++);
            String parameter = lhsOpDescription.getType().getOptionValueTypeParameterisation();
            ruleStore.addContainedClass(createSpecificExpression(expressionName, parameter, desc.getValue()));
            constructor.addStatement(ruleName + ".addAction(new Action<" + parameter + ">(\"" + desc.getOptionIdentifier() + "\", new " + expressionName +  "()))");
          }
        }
      }
    }

    for (OverrideRuleDescription ruleDesc : dslInfo.getOverrideRuleDescriptions()) {
      String id = getUniqueID();
      String ruleName = "rule" + id;
      String conditionName = "rule" + id + "Condition";
      String conditionText = ruleDesc.getConditionText();

      if (conditionText == null || conditionText.equals("")) {
        constructor.addStatement("Rule " + ruleName + " = new OverrideRule(Expression.TRUE)");
      } else {
        String conditionTypeName = "Rule" + id + "Condition";
        constructor.addStatement("Expression<Boolean> " + conditionName + " = new " + conditionTypeName + "()");
        ruleStore.addContainedClass(createSpecificExpression(conditionTypeName, "Boolean", conditionText));
        constructor.addStatement("Rule " + ruleName + " = new OverrideRule(" + conditionName + ")");
      }

      int count = 1;
      for (AssignmentDescription desc : ruleDesc.getAssignments()) {
        OptionDescription lhsOpDescription = dslInfo.getOptionDescriptionForIdentifier(desc.getOptionIdentifier());
        if (lhsOpDescription == null) {
          System.out.println("Error, option " + desc.getOptionIdentifier() + " not found for assignment in fly rule");
        } else {
          String expressionName = "Rule" + id + "Expression" + (count++);
          String parameter = lhsOpDescription.getType().getOptionValueTypeParameterisation();
          ruleStore.addContainedClass(createSpecificExpression(expressionName, parameter, desc.getValue()));
          constructor.addStatement(ruleName + ".addAction(new Action<" + parameter + ">(\"" + desc.getOptionIdentifier() + "\", new " + expressionName +  "()))");
        }
      }
    }

    for (ValidityRuleDescription validityDesc : dslInfo.getValidityRuleDescriptions()) {
      String id = getUniqueID();
      String ruleName = "rule" + id;
      String conditionName = "rule" + id + "Condition";
      String conditionText = validityDesc.getConditionText();

      if (conditionText == null || conditionText.equals("")) {
        System.out.println("Error, no condition for validity rule.");
      } else {
        String conditionTypeName = "Rule" + id + "Condition";
        constructor.addStatement("Expression<Boolean> " + conditionName + " = new " + conditionTypeName + "()");
        ruleStore.addContainedClass(createSpecificExpression(conditionTypeName, "Boolean", conditionText));
        constructor.addStatement("Rule " + ruleName + " = new ValidityRule(" + conditionName + ")");
      }

      String expressionName = "Rule" + id + "Expression";
      String parameter = "java.util.List<String>";
      String contents = "java.util.Arrays.asList(\"" + validityDesc.getExplanation() + "\")";
      ruleStore.addContainedClass(createSpecificExpression(expressionName, parameter, contents));
      constructor.addStatement(ruleName + ".addAction(new Action<" + parameter + ">(\"CLOPSERROROPTION\", new " + expressionName +  "()))");

    }

    return ruleStore;
  }

  private static GeneratedClassOrInterface createSpecificExpression(String name, String type, String conditionText) {
    GeneratedClassOrInterface condition = new GeneratedClassOrInterface(name, false, null, Visibility.Public);
    condition.addModifier("static");
    condition.addImplementedInterface("ie.ucd.clops.runtime.rules.Expression<" + type + ">");

    GeneratedMethod evaluate = new GeneratedMethod("evaluate", type, Visibility.Public);
    evaluate.addArg(new GeneratedArgument("optionStore", "ie.ucd.clops.runtime.options.OptionStore"));
    evaluate.addStatement("return " + conditionText);
    condition.addMethod(evaluate);

    return condition;
  }

  /*private static GeneratedClassOrInterface createSpecificAction(String name, String optionName, String actionText) {
    GeneratedClassOrInterface condition = new GeneratedClassOrInterface(name, false, null, Visibility.Public);
    condition.addModifier("static");
    condition.addImplementedInterface("ie.ucd.clops.runtime.rules.Action");

    GeneratedMethod evaluate = new GeneratedMethod("perform", "void", Visibility.Public);
    evaluate.addArg(new GeneratedArgument("optionStore", "ie.ucd.clops.runtime.options.OptionStore"));

    evaluate.addStatement("optionStore.getOptionByIdentifier(\"" + optionName + "\").set("  + actionText + ")");

    condition.addMethod(evaluate);

    return condition;
  }*/

  private static int counter = 1;
  private static String getUniqueID() {
    return "" + counter++;
  }

  private static GeneratedClassOrInterface createOptionsInterface(String parserName, Collection<OptionDescription> opDescriptions, String outputPackage) {
    GeneratedClassOrInterface optionsInterface = new GeneratedClassOrInterface(parserName + "OptionsInterface", true, outputPackage, Visibility.Public);
    for (OptionDescription od : opDescriptions) {
      GeneratedMethod isSetMethod = new GeneratedMethod(Namer.getIsSetMethodName(od), "boolean", Visibility.Public);
      isSetMethod.setAbstract(true);
      GeneratedMethod getValueMethod = new GeneratedMethod(Namer.getGetValueMethodName(od), od.getType().getOptionValueTypeClass(), Visibility.Public);
      getValueMethod.setAbstract(true);
      optionsInterface.addMethod(isSetMethod);
      optionsInterface.addMethod(getValueMethod);
    }
    return optionsInterface;
  }

  private static GeneratedClassOrInterface createSpecificParser(
      String parserName, 
      String formatString,
      Collection<OptionDescription> opDescriptions, 
      Collection<OptionGroupDescription> opGroupDescriptions,
      Collection<FlyRuleDescription> overrideRuleDescriptions,
      String outputPackage) {
    GeneratedClassOrInterface specificParser = new GeneratedClassOrInterface(parserName + "Parser", false, outputPackage, Visibility.Public);

    GeneratedField optionStore = new GeneratedField("optionStore", getQualifiedClassName(parserName + "OptionStore", outputPackage));
    optionStore.addModifier("final");
    specificParser.addField(optionStore);
    specificParser.addMethod(createGetter(optionStore));

    GeneratedField ruleStore = new GeneratedField("ruleStore", "ie.ucd.clops.runtime.rules.RuleStore");
    optionStore.addModifier("final");
    specificParser.addMethod(createGetter(ruleStore));
    specificParser.addField(ruleStore);

    specificParser.setSuperClass("ie.ucd.clops.runtime.parser.AbstractSpecificCLParser");
    GeneratedMethod constructor = new GeneratedConstructor(parserName + "Parser", Visibility.Public);
    constructor.addException("ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException");
    constructor.addStatement("optionStore = createOptionStore()");
    constructor.addStatement("ruleStore = createRuleStore()");
    specificParser.addMethod(constructor);

    //Create the method that will initialise the OptionStore
    specificParser.addMethod(createOptionInitialisationMethod(parserName, outputPackage, specificParser, opDescriptions, opGroupDescriptions));

    //Create the method that will initialise the override rules
    createRuleInitialisationCode(specificParser, parserName);

    GeneratedMethod createFormat = new GeneratedMethod("getFormatString", "String", Visibility.Public);
    createFormat.addStatement("return \"" + formatString + "\"");
    specificParser.addMethod(createFormat);
    return specificParser;
  }

  private static GeneratedClassOrInterface createSpecificOptionStore(
      String parserName,
      Collection<OptionDescription> opDescriptions, 
      Collection<OptionGroupDescription> opGroupDescriptions,
      String outputPackage) {
    final String className = "OptionStore";

    GeneratedClassOrInterface specificOptionStore = new GeneratedClassOrInterface(parserName + className, false, outputPackage, Visibility.Public);
    specificOptionStore.setSuperClass("ie.ucd.clops.runtime.options.OptionStore");
    specificOptionStore.addImplementedInterface(parserName + "OptionsInterface");
    specificOptionStore.addImport("ie.ucd.clops.runtime.options.OptionGroup");

    for (OptionDescription opDesc : opDescriptions) {
      GeneratedField field = new GeneratedField(Namer.getOptionInstanceName(opDesc), opDesc.getType().getOptionTypeClass(), Visibility.Private);
      field.addModifier("final");
      specificOptionStore.addField(field);
    }
    GeneratedField field = new GeneratedField(CLOPSErrorOption.ERROR_OPTION_ID, "ie.ucd.clops.runtime.options.CLOPSErrorOption", Visibility.Private);
    field.addModifier("final");
    specificOptionStore.addField(field);

    GeneratedConstructor constructor = new GeneratedConstructor(parserName + className, Visibility.Public);
    constructor.addException("ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException");

    //Create and add each Option
    for (OptionDescription opDesc : opDescriptions) {
      constructor.addStatement(Namer.getOptionInstanceName(opDesc) + " = new " + opDesc.getType().getOptionTypeClass() + "(\"" + opDesc.getIdentifier() + "\", \"" + OptionType.unifyRegexps(opDesc.getPrefixRegexps()) + "\")"); 

      for (Pair<String,String> entry : opDesc.getProperties()) {
        constructor.addStatement(Namer.getOptionInstanceName(opDesc) + ".setProperty(\"" + entry.getFirst() + "\",\"" + entry.getSecond() + "\")");
      }
      if (opDesc.getDescription() != null) {
        String desc = quoteMultilineString(opDesc.getDescription());
        constructor.addStatement(Namer.getOptionInstanceName(opDesc) + ".setProperty(\"description\", " + desc + ")");
      }
      constructor.addStatement("addOption(" + Namer.getOptionInstanceName(opDesc) + ")");
    }
    constructor.addStatement(CLOPSErrorOption.ERROR_OPTION_ID + " = new ie.ucd.clops.runtime.options.CLOPSErrorOption()");
    constructor.addStatement("addOption(" + CLOPSErrorOption.ERROR_OPTION_ID + ")");

    //Create and add each OptionGroup
    for (OptionGroupDescription opGroupDesc : opGroupDescriptions) {
      constructor.addStatement("OptionGroup " + Namer.getOptionGroupInstanceName(opGroupDesc) + " = new OptionGroup(\"" + opGroupDesc.getIdentifier() + "\")");
      constructor.addStatement("addOptionGroup(" + Namer.getOptionGroupInstanceName(opGroupDesc) + ")");
    }

    //Loop again, this time adding the children
    for (OptionGroupDescription opGroupDesc : opGroupDescriptions) {
      for (String child : opGroupDesc.getChildren()) {
        constructor.addStatement(Namer.getOptionGroupInstanceName(opGroupDesc) + ".addOptionOrGroup(" + Namer.getOptionGroupChildInstanceName(child) + ")");
      }
    }

    specificOptionStore.addMethod(constructor);


    for (OptionDescription od : opDescriptions) {
      GeneratedMethod isSetMethod = new GeneratedMethod(Namer.getIsSetMethodName(od), "boolean", Visibility.Public);
      isSetMethod.addStatement("return " + Namer.getOptionInstanceName(od) + ".hasValue()");
      specificOptionStore.addMethod(isSetMethod);
      GeneratedMethod getValueMethod = new GeneratedMethod(Namer.getGetValueMethodName(od), od.getType().getOptionValueTypeClass(), Visibility.Public);
      getValueMethod.addStatement("return " + Namer.getOptionInstanceName(od) + ".getValue()");
      specificOptionStore.addMethod(getValueMethod);
      GeneratedMethod getOptionMethod = new GeneratedMethod(Namer.getGetOptionMethodName(od), od.getType().getOptionTypeClass(), Visibility.Public);
      getOptionMethod.addStatement("return " + Namer.getOptionInstanceName(od));
      specificOptionStore.addMethod(getOptionMethod);
    }

    return specificOptionStore;
  }

  private static GeneratedClassOrInterface createTester(String parserName, String outputPackage) {
    GeneratedClassOrInterface tester = new GeneratedClassOrInterface("Main", false, outputPackage, Visibility.Public);
    tester.addImport("java.util.logging.Level");
    tester.addImport("ie.ucd.clops.logging.CLOLogger");
    tester.addImport("ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException");

    GeneratedMethod main = new GeneratedMethod("main", "void", Visibility.Public);
    main.addException("Exception");
    main.addModifier("static");
    main.addArg(new GeneratedArgument("args", "String[]"));
    main.addStatement("CLOLogger.setLogLevel(Level.FINE)");


    main.addStatement(parserName + "Parser parser = new " + parserName + "Parser()");
    main.addStatement("boolean success = parser.parse(args)");

    main.addStatement("if (success) {", false);
    main.addStatement("  CLOLogger.getLogger().log(Level.INFO, \"Successful parse.\")");
    main.addStatement("} else {", false);
    main.addStatement("  CLOLogger.getLogger().log(Level.INFO, \"Parse did not succeed.\")");
    main.addStatement("}", false);

    tester.addMethod(main);

    return tester;
  }

  private static GeneratedMethod createGetter(GeneratedField field) {
    String methodName = "get" + Character.toUpperCase(field.getName().charAt(0)) + field.getName().substring(1);
    return createGetter(field, methodName);
  }

  private static GeneratedMethod createGetter(GeneratedField field, String methodName) {
    GeneratedMethod method = new GeneratedMethod(methodName, field.getType(), Visibility.Public);
    method.addStatement("return " + field.getName());
    return method;
  }

  private static String getQualifiedClassName(String name, String packageName) {
    if (packageName.equals("")) {
      return name;
    } else {
      return packageName + '.' + name;
    }
  }

}
