////////////////////////////////////////////////////////////////
//
// template
//
////////////////////////////////////////////////////////////////

using System;
using Microsoft.Singularity.UnitTest;
using Microsoft.Singularity.Transform;

namespace Microsoft.Singularity.UnitTest
{
    //
    // template for generating jig
    //

    /// Pattern to match test classes
    [Pattern]
    [TestClass]
    internal class EachTestClass : TestClass
    {
        // each class should have a no-argument constructor
        internal EachTestClass() { }

        [Pattern]
        [ClassInitialize]
        internal void EachInitMethod() { }

        [Pattern]
        [TestMethod]
        internal void EachTestMethod() { }
    }

    /// template for generated code per test class
    [Template]
    internal class EachTestClass_Jig : SuiteJig
    {
        private EachTestClass! m_test;

        public EachTestClass_Jig(TestLog! log)
        {
            EachTestClass t = new EachTestClass();
            t.SetLog(log);
            m_test = t;
        }

        public override void Initialize()
        {
            Transform.For("EachInitMethod");
            m_test.EachInitMethod();
            Transform.EndFor();
        }
        
        public override void DoTest(string! name)
        {
            Transform.For("EachTestMethod");
            if (name.Equals("EachTestMethod")) {
                m_test.EachTestMethod();
                return;
            }
            Transform.EndFor();
            base.DoTest(name);
        }
    }

    /// template for generated code for entire module
    [Template]
    public class TheModuleJig : ModuleJig
    {
        public TheModuleJig()
        {
        }

        public override SuiteJig GetSuite(string! name, TestLog! log)
        {
            Transform.For("EachTestClass");
            if ("EachTestClass".EndsWith(name)) {
                return new EachTestClass_Jig(log);
            }
            Transform.EndFor();
            return base.GetSuite(name, log);
        }
    }
}

