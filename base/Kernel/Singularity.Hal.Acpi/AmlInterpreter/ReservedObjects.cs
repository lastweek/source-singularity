///////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

using System.Diagnostics;
using Microsoft.Singularity.Hal.Acpi.AcpiObject;
using Node = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.Node;
using AbsoluteNodePath = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.AbsoluteNodePath;

namespace Microsoft.Singularity.Hal.Acpi
{
    public class ReservedObjects
    {
        AcpiNamespace acpiNamespace;

        public ReservedObjects(AcpiNamespace acpiNamespace)
        {
            this.acpiNamespace = acpiNamespace;
        }

        public void CreateReservedObjects()
        {
            AddNamespace("_GPE");
            AddNamespace("_PR_");
            AddNamespace("_SB_");
            AddNamespace("_SI_");
            AddNamespace("_TZ_");

            AddMethod("_BCM", 1, _BCM);
            AddMethod("_BLT", 3, _BLT);
            AddMethod("_BMC", 1, _BMC);
            AddMethod("_BTM", 1, _BTM);
            AddMethod("_BTP", 1, _BTP);
            AddMethod("_DCK", 1, _DCK);
            AddMethod("_DDC", 1, _DDC);
            AddMethod("_DOS", 1, _DOS);
            AddMethod("_DSM", 4, _DSM);
            AddMethod("_DSS", 1, _DSS);
            AddMethod("_DSW", 3, _DSW);
            AddMethod("_FDM", 2, _FDM);
            AddMethod("_MSG", 1, _MSG);
            AddMethod("_OSC", 4, _OSC);
            AddMethod("_OSI", 1, _OSI);
            AddMethod("_OST", 1, _OST);
            AddMethod("_PDC", 1, _PDC);
            AddMethod("_PSW", 1, _PSW);
            AddMethod("_REG", 2, _REG);
            AddMethod("_ROM", 2, _ROM);
            AddMethod("_SCP", 3, _SCP);
            AddMethod("_SDD", 1, _SDD);
            AddMethod("_SPD", 1, _SPD);
            AddMethod("_SRS", 1, _SRS);
            AddMethod("_SST", 1, _SST);
            AddMethod("_STM", 3, _STM);
            AddMethod("_TPT", 1, _TPT);
        }

        private void AddNamespace(string name)
        {
            AbsoluteNodePath root = AbsoluteNodePath.CreateRoot();
            acpiNamespace.CreateNodeAt(new AbsoluteNodePath(new string[] { name } ), root);
        }

        private void AddMethod(string name, byte numArgs, ReservedMethod.AcpiMethodImpl impl)
        {
            AbsoluteNodePath root = AbsoluteNodePath.CreateRoot();
            Node node = acpiNamespace.CreateNodeAt(new AbsoluteNodePath(new string[] { name } ), root);
            node.Value = new ReservedMethod(numArgs, SerializeFlag.NotSerialized, 0 /*syncLevel*/, impl);;
        }

        private AcpiObject.AcpiObject _OSI(AcpiObject.AcpiObject[] args)
        {
            if (args.Length > 0 && args[0].GetAsString().Value == "Singularity") {
                return new Integer(1);
            }
            else {
                return new Integer(0);
            }
        }

        private AcpiObject.AcpiObject _OSC(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _SRS(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _OST(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _DCK(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _REG(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _DSW(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _PSW(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _PDC(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _SST(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _MSG(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _BLT(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _STM(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _SDD(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _FDM(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _DSM(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _BTP(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _BTM(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _BMC(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _SCP(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _TPT(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _DOS(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _ROM(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _SPD(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _BCM(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _DDC(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }

        private AcpiObject.AcpiObject _DSS(AcpiObject.AcpiObject[] args)
        {
            Debug.Assert(false, "Not yet implemented");
            return new AcpiObject.UninitializedObject();
        }
    }
}
