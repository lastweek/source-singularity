// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//=====================================================================
//=====================================================================  


using System;
using System.Threading;
using System.Reflection;
using System.Reflection.Emit;

public class App {
    public static void Main(String[] args) {
        AssemblyBuilder assembly;

        assembly = (AssemblyBuilder) CreateCallee(Thread.GetDomain(), AssemblyBuilderAccess.Save).Assembly;
        assembly.Save("EmittedAssembly.dll");
    }

    // Create the callee transient dynamic assembly.
    private static Type CreateCallee(AppDomain appDomain) {
        // Create a simple name for the callee assembly.
        AssemblyName assemblyName = new AssemblyName();
        assemblyName.Name = "EmittedAssembly";

        // Create the callee dynamic assembly.
        AssemblyBuilder assembly = appDomain.DefineDynamicAssembly(assemblyName, AssemblyBuilderAccess.Save);

        // Create a dynamic module named "CalleeModule" in the callee assembly.
        ModuleBuilder module;
        module = assembly.DefineDynamicModule("EmittedModule", "EmittedModule.mod");

        // Define a public class named "HelloWorld" in the assembly.
        TypeBuilder helloWorldClass = module.DefineType("HelloWorld", TypeAttributes.Public);

        // Define a private String field named "Greeting" in the type.
        FieldBuilder greetingField = helloWorldClass.DefineField("Greeting", typeof(String), FieldAttributes.Private);

        // Create the constructor.
        Type[] constructorArgs = { typeof(String) };
        ConstructorBuilder constructor = helloWorldClass.DefineConstructor(
            MethodAttributes.Public, CallingConventions.Standard, constructorArgs);

        // Generate IL for the method. The constructor calls its superclass
        // constructor. The constructor stores its argument in the private field.
        ILGenerator constructorIL = constructor.GetILGenerator();
        constructorIL.Emit(OpCodes.Ldarg_0);
        ConstructorInfo superConstructor = typeof(Object).GetConstructor(new Type[0]);
        constructorIL.Emit(OpCodes.Call, superConstructor);
        constructorIL.Emit(OpCodes.Ldarg_0);
        constructorIL.Emit(OpCodes.Ldarg_1);
        constructorIL.Emit(OpCodes.Stfld, greetingField);
        constructorIL.Emit(OpCodes.Ret);

        // Create the GetGreeting method.
        MethodBuilder getGreetingMethod = helloWorldClass.DefineMethod("GetGreeting",
                                                                       MethodAttributes.Public, typeof(String), null);

        // Generate IL for GetGreeting.
        ILGenerator methodIL = getGreetingMethod.GetILGenerator();
        methodIL.Emit(OpCodes.Ldarg_0);
        methodIL.Emit(OpCodes.Ldfld, greetingField);
        methodIL.Emit(OpCodes.Ret);

        // Bake the class HelloWorld.
        return(helloWorldClass.CreateType());
    }
}

