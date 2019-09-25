///////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

using System;
using System.Diagnostics;
using System.Text;

using Microsoft.Singularity.Hal.Acpi.AmlParserUnions;

namespace Microsoft.Singularity.Hal.Acpi
{
    /// <summary>
    /// This abstract node visitor class (following the GoF Visitor pattern) enables
    /// straightforward structural recursion over an AML parse tree, which is useful in
    /// the parser and interpreter. Leaf classes are left abstract and must be implemented.
    /// </summary>
    public abstract class AmlParserNodeVisitor
    {
        public abstract void UnhandledNodeType(string nodeTypeName);

        public virtual void Visit(SimpleName simpleName)
        {
            simpleName.AcceptAlternative(this);
        }

        public virtual void Visit(SuperName superName)
        {
            superName.AcceptAlternative(this);
        }

        public virtual void Visit(ComputationalData computationalData)
        {
            computationalData.AcceptAlternative(this);
        }

        public virtual void Visit(DataObject dataObject)
        {
            dataObject.AcceptAlternative(this);
        }

        public virtual void Visit(DataRefObject dataRefObject)
        {
            dataRefObject.AcceptAlternative(this);
        }

        public virtual void Visit(TermObj termObj)
        {
            termObj.AcceptAlternative(this);
        }

        public virtual void Visit(TermArg termArg)
        {
            termArg.AcceptAlternative(this);
        }

        public virtual void Visit(AmlObject amlObject)
        {
            amlObject.AcceptAlternative(this);
        }

        public virtual void Visit(NameSpaceModifierObj nameSpaceModifierObj)
        {
            nameSpaceModifierObj.AcceptAlternative(this);
        }

        public virtual void Visit(NamedObj namedObj)
        {
            namedObj.AcceptAlternative(this);
        }

        public virtual void Visit(FieldElement fieldElement)
        {
            fieldElement.AcceptAlternative(this);
        }

        public virtual void VisitType1Opcode(Type1Opcode type1Opcode)
        {
            type1Opcode.AcceptAlternative(this);
        }

        public virtual void VisitType2Opcode(Type2Opcode type2Opcode)
        {
            type2Opcode.AcceptAlternative(this);
        }

        public virtual void VisitType6Opcode(Type6Opcode type6Opcode)
        {
            type6Opcode.AcceptAlternative(this);
        }

        public virtual void Visit(PackageElement packageElement)
        {
            packageElement.AcceptAlternative(this);
        }

        public virtual void Visit(AmlParser.AMLCode amlCode)
        {
            UnhandledNodeType("AMLCode");
        }

        public virtual void Visit(AmlParser.NameSeg nameSeg)
        {
            UnhandledNodeType("NameSeg");
        }

        public virtual void Visit(AmlParser.NameString nameString)
        {
            UnhandledNodeType("NameString");
        }

        public virtual void Visit(AmlParser.PrefixPath prefixPath)
        {
            UnhandledNodeType("PrefixPath");
        }

        public virtual void Visit(AmlParser.NamePath namePath)
        {
            UnhandledNodeType("NamePath");
        }

        public virtual void Visit(AmlParser.SegCount segCount)
        {
            UnhandledNodeType("SegCount");
        }

        public virtual void Visit(AmlParser.Target target)
        {
            UnhandledNodeType("Target");
        }

        public virtual void Visit(AmlParser.ConstObj constObj)
        {
            UnhandledNodeType("ConstObj");
        }

        public virtual void Visit(AmlParser.UserTermObj userTermObj)
        {
            UnhandledNodeType("UserTermObj");
        }

        public virtual void Visit(AmlParser.DefAlias defAlias)
        {
            UnhandledNodeType("DefAlias");
        }

        public virtual void Visit(AmlParser.DefName defName)
        {
            UnhandledNodeType("DefName");
        }

        public virtual void Visit(AmlParser.DefScope defScope)
        {
            UnhandledNodeType("DefScope");
        }

        public virtual void Visit(AmlParser.DefBankField defBankField)
        {
            UnhandledNodeType("DefBankField");
        }

        public virtual void Visit(AmlParser.BankValue bankValue)
        {
            UnhandledNodeType("BankValue");
        }

        public virtual void Visit(AmlParser.FieldFlags fieldFlags)
        {
            UnhandledNodeType("FieldFlags");
        }

        public virtual void Visit(AmlParser.NamedField namedField)
        {
            UnhandledNodeType("NamedField");
        }

        public virtual void Visit(AmlParser.ReservedField reservedField)
        {
            UnhandledNodeType("ReservedField");
        }

        public virtual void Visit(AmlParser.AccessField accessField)
        {
            UnhandledNodeType("AccessField");
        }

        public virtual void Visit(AmlParser.DefCreateBitField defCreateBitField)
        {
            UnhandledNodeType("DefCreateBitField");
        }

        public virtual void Visit(AmlParser.SourceBuff sourceBuff)
        {
            UnhandledNodeType("SourceBuff");
        }

        public virtual void Visit(AmlParser.BitIndex bitIndex)
        {
            UnhandledNodeType("BitIndex");
        }

        public virtual void Visit(AmlParser.DefCreateByteField defCreateByteField)
        {
            UnhandledNodeType("DefCreateByteField");
        }

        public virtual void Visit(AmlParser.ByteIndex byteIndex)
        {
            UnhandledNodeType("ByteIndex");
        }

        public virtual void Visit(AmlParser.DefCreateDWordField defCreateDWordField)
        {
            UnhandledNodeType("DefCreateDWordField");
        }

        public virtual void Visit(AmlParser.DefCreateField defCreateField)
        {
            UnhandledNodeType("DefCreateField");
        }

        public virtual void Visit(AmlParser.NumBits numBits)
        {
            UnhandledNodeType("NumBits");
        }

        public virtual void Visit(AmlParser.DefCreateQWordField defCreateQWordField)
        {
            UnhandledNodeType("DefCreateQWordField");
        }

        public virtual void Visit(AmlParser.DefCreateWordField defCreateWordField)
        {
            UnhandledNodeType("DefCreateWordField");
        }

        public virtual void Visit(AmlParser.DefDataRegion defDataRegion)
        {
            UnhandledNodeType("DefDataRegion");
        }

        public virtual void Visit(AmlParser.DefDevice defDevice)
        {
            UnhandledNodeType("DefDevice");
        }

        public virtual void Visit(AmlParser.DefEvent defEvent)
        {
            UnhandledNodeType("DefEvent");
        }

        public virtual void Visit(AmlParser.DefField defField)
        {
            UnhandledNodeType("DefField");
        }

        public virtual void Visit(AmlParser.DefIndexField defIndexField)
        {
            UnhandledNodeType("DefIndexField");
        }

        public virtual void Visit(AmlParser.DefMethod defMethod)
        {
            UnhandledNodeType("DefMethod");
        }

        public virtual void Visit(AmlParser.MethodFlags methodFlags)
        {
            UnhandledNodeType("MethodFlags");
        }

        public virtual void Visit(AmlParser.DefMutex defMutex)
        {
            UnhandledNodeType("DefMutex");
        }

        public virtual void Visit(AmlParser.SyncFlags syncFlags)
        {
            UnhandledNodeType("SyncFlags");
        }

        public virtual void Visit(AmlParser.DefOpRegion defOpRegion)
        {
            UnhandledNodeType("DefOpRegion");
        }

        public virtual void Visit(AmlParser.RegionSpace regionSpace)
        {
            UnhandledNodeType("RegionSpace");
        }

        public virtual void Visit(AmlParser.RegionOffset regionOffset)
        {
            UnhandledNodeType("RegionOffset");
        }

        public virtual void Visit(AmlParser.RegionLen regionLen)
        {
            UnhandledNodeType("RegionLen");
        }

        public virtual void Visit(AmlParser.DefPowerRes defPowerRes)
        {
            UnhandledNodeType("DefPowerRes");
        }

        public virtual void Visit(AmlParser.SystemLevel systemLevel)
        {
            UnhandledNodeType("SystemLevel");
        }

        public virtual void Visit(AmlParser.ResourceOrder resourceOrder)
        {
            UnhandledNodeType("ResourceOrder");
        }

        public virtual void Visit(AmlParser.DefProcessor defProcessor)
        {
            UnhandledNodeType("DefProcessor");
        }

        public virtual void Visit(AmlParser.ProcID procID)
        {
            UnhandledNodeType("ProcID");
        }

        public virtual void Visit(AmlParser.PblkAddr pblkAddr)
        {
            UnhandledNodeType("PblkAddr");
        }

        public virtual void Visit(AmlParser.PblkLen pblkLen)
        {
            UnhandledNodeType("PblkLen");
        }

        public virtual void Visit(AmlParser.DefThermalZone defThermalZone)
        {
            UnhandledNodeType("DefThermalZone");
        }

        public virtual void Visit(AmlParser.DefBreak defBreak)
        {
            UnhandledNodeType("DefBreak");
        }

        public virtual void Visit(AmlParser.DefBreakPoint defBreakPoint)
        {
            UnhandledNodeType("DefBreakPoint");
        }

        public virtual void Visit(AmlParser.DefContinue defContinue)
        {
            UnhandledNodeType("DefContinue");
        }

        public virtual void Visit(AmlParser.DefElse defElse)
        {
            UnhandledNodeType("DefElse");
        }

        public virtual void Visit(AmlParser.DefFatal defFatal)
        {
            UnhandledNodeType("DefFatal");
        }

        public virtual void Visit(AmlParser.FatalType fatalType)
        {
            UnhandledNodeType("FatalType");
        }

        public virtual void Visit(AmlParser.FatalCode fatalCode)
        {
            UnhandledNodeType("FatalCode");
        }

        public virtual void Visit(AmlParser.FatalArg fatalArg)
        {
            UnhandledNodeType("FatalArg");
        }

        public virtual void Visit(AmlParser.DefIfElse defIfElse)
        {
            UnhandledNodeType("DefIfElse");
        }

        public virtual void Visit(AmlParser.Predicate predicate)
        {
            UnhandledNodeType("Predicate");
        }

        public virtual void Visit(AmlParser.DefLoad defLoad)
        {
            UnhandledNodeType("DefLoad");
        }

        public virtual void Visit(AmlParser.DDBHandleObject dDBHandleObject)
        {
            UnhandledNodeType("DDBHandleObject");
        }

        public virtual void Visit(AmlParser.DefNoop defNoop)
        {
            UnhandledNodeType("DefNoop");
        }

        public virtual void Visit(AmlParser.DefNotify defNotify)
        {
            UnhandledNodeType("DefNotify");
        }

        public virtual void Visit(AmlParser.NotifyObject notifyObject)
        {
            UnhandledNodeType("NotifyObject");
        }

        public virtual void Visit(AmlParser.NotifyValue notifyValue)
        {
            UnhandledNodeType("NotifyValue");
        }

        public virtual void Visit(AmlParser.DefRelease defRelease)
        {
            UnhandledNodeType("DefRelease");
        }

        public virtual void Visit(AmlParser.MutexObject mutexObject)
        {
            UnhandledNodeType("MutexObject");
        }

        public virtual void Visit(AmlParser.DefReset defReset)
        {
            UnhandledNodeType("DefReset");
        }

        public virtual void Visit(AmlParser.EventObject eventObject)
        {
            UnhandledNodeType("EventObject");
        }

        public virtual void Visit(AmlParser.DefReturn defReturn)
        {
            UnhandledNodeType("DefReturn");
        }

        public virtual void Visit(AmlParser.ArgObject argObject)
        {
            UnhandledNodeType("ArgObject");
        }

        public virtual void Visit(AmlParser.DefSignal defSignal)
        {
            UnhandledNodeType("DefSignal");
        }

        public virtual void Visit(AmlParser.DefSleep defSleep)
        {
            UnhandledNodeType("DefSleep");
        }

        public virtual void Visit(AmlParser.MsecTime msecTime)
        {
            UnhandledNodeType("MsecTime");
        }

        public virtual void Visit(AmlParser.DefStall defStall)
        {
            UnhandledNodeType("DefStall");
        }

        public virtual void Visit(AmlParser.UsecTime usecTime)
        {
            UnhandledNodeType("UsecTime");
        }

        public virtual void Visit(AmlParser.DefUnload defUnload)
        {
            UnhandledNodeType("DefUnload");
        }

        public virtual void Visit(AmlParser.DefWhile defWhile)
        {
            UnhandledNodeType("DefWhile");
        }

        public virtual void Visit(AmlParser.DefAcquire defAcquire)
        {
            UnhandledNodeType("DefAcquire");
        }

        public virtual void Visit(AmlParser.TimeOut timeOut)
        {
            UnhandledNodeType("TimeOut");
        }

        public virtual void Visit(AmlParser.DefAdd defAdd)
        {
            UnhandledNodeType("DefAdd");
        }

        public virtual void Visit(AmlParser.Operand operand)
        {
            UnhandledNodeType("Operand");
        }

        public virtual void Visit(AmlParser.DefAnd defAnd)
        {
            UnhandledNodeType("DefAnd");
        }

        public virtual void Visit(AmlParser.DefBuffer defBuffer)
        {
            UnhandledNodeType("DefBuffer");
        }

        public virtual void Visit(AmlParser.BufferSize bufferSize)
        {
            UnhandledNodeType("BufferSize");
        }

        public virtual void Visit(AmlParser.DefConcat defConcat)
        {
            UnhandledNodeType("DefConcat");
        }

        public virtual void Visit(AmlParser.Data data)
        {
            UnhandledNodeType("Data");
        }

        public virtual void Visit(AmlParser.DefConcatRes defConcatRes)
        {
            UnhandledNodeType("DefConcatRes");
        }

        public virtual void Visit(AmlParser.BufData bufData)
        {
            UnhandledNodeType("BufData");
        }

        public virtual void Visit(AmlParser.DefCondRefOf defCondRefOf)
        {
            UnhandledNodeType("DefCondRefOf");
        }

        public virtual void Visit(AmlParser.DefCopyObject defCopyObject)
        {
            UnhandledNodeType("DefCopyObject");
        }

        public virtual void Visit(AmlParser.DefDecrement defDecrement)
        {
            UnhandledNodeType("DefDecrement");
        }

        public virtual void Visit(AmlParser.DefDerefOf defDerefOf)
        {
            UnhandledNodeType("DefDerefOf");
        }

        public virtual void Visit(AmlParser.ObjReference objReference)
        {
            UnhandledNodeType("ObjReference");
        }

        public virtual void Visit(AmlParser.DefDivide defDivide)
        {
            UnhandledNodeType("DefDivide");
        }

        public virtual void Visit(AmlParser.Dividend dividend)
        {
            UnhandledNodeType("Dividend");
        }

        public virtual void Visit(AmlParser.Divisor divisor)
        {
            UnhandledNodeType("Divisor");
        }

        public virtual void Visit(AmlParser.Remainder remainder)
        {
            UnhandledNodeType("Remainder");
        }

        public virtual void Visit(AmlParser.Quotient quotient)
        {
            UnhandledNodeType("Quotient");
        }

        public virtual void Visit(AmlParser.DefFindSetLeftBit defFindSetLeftBit)
        {
            UnhandledNodeType("DefFindSetLeftBit");
        }

        public virtual void Visit(AmlParser.DefFindSetRightBit defFindSetRightBit)
        {
            UnhandledNodeType("DefFindSetRightBit");
        }

        public virtual void Visit(AmlParser.DefFromBCD defFromBCD)
        {
            UnhandledNodeType("DefFromBCD");
        }

        public virtual void Visit(AmlParser.BCDValue bCDValue)
        {
            UnhandledNodeType("BCDValue");
        }

        public virtual void Visit(AmlParser.DefIncrement defIncrement)
        {
            UnhandledNodeType("DefIncrement");
        }

        public virtual void Visit(AmlParser.DefIndex defIndex)
        {
            UnhandledNodeType("DefIndex");
        }

        public virtual void Visit(AmlParser.BuffPkgStrObj buffPkgStrObj)
        {
            UnhandledNodeType("BuffPkgStrObj");
        }

        public virtual void Visit(AmlParser.IndexValue indexValue)
        {
            UnhandledNodeType("IndexValue");
        }

        public virtual void Visit(AmlParser.DefLAnd defLAnd)
        {
            UnhandledNodeType("DefLAnd");
        }

        public virtual void Visit(AmlParser.DefLEqual defLEqual)
        {
            UnhandledNodeType("DefLEqual");
        }

        public virtual void Visit(AmlParser.DefLGreater defLGreater)
        {
            UnhandledNodeType("DefLGreater");
        }

        public virtual void Visit(AmlParser.DefLGreaterEqual defLGreaterEqual)
        {
            UnhandledNodeType("DefLGreaterEqual");
        }

        public virtual void Visit(AmlParser.DefLLess defLLess)
        {
            UnhandledNodeType("DefLLess");
        }

        public virtual void Visit(AmlParser.DefLLessEqual defLLessEqual)
        {
            UnhandledNodeType("DefLLessEqual");
        }

        public virtual void Visit(AmlParser.DefLNot defLNot)
        {
            UnhandledNodeType("DefLNot");
        }

        public virtual void Visit(AmlParser.DefLNotEqual defLNotEqual)
        {
            UnhandledNodeType("DefLNotEqual");
        }

        public virtual void Visit(AmlParser.DefLoadTable defLoadTable)
        {
            UnhandledNodeType("DefLoadTable");
        }

        public virtual void Visit(AmlParser.DefLOr defLOr)
        {
            UnhandledNodeType("DefLOr");
        }

        public virtual void Visit(AmlParser.DefMatch defMatch)
        {
            UnhandledNodeType("DefMatch");
        }

        public virtual void Visit(AmlParser.SearchPkg searchPkg)
        {
            UnhandledNodeType("SearchPkg");
        }

        public virtual void Visit(AmlParser.StartIndex startIndex)
        {
            UnhandledNodeType("StartIndex");
        }

        public virtual void Visit(AmlParser.DefMid defMid)
        {
            UnhandledNodeType("DefMid");
        }

        public virtual void Visit(AmlParser.MidObj midObj)
        {
            UnhandledNodeType("MidObj");
        }

        public virtual void Visit(AmlParser.DefMod defMod)
        {
            UnhandledNodeType("DefMod");
        }

        public virtual void Visit(AmlParser.DefMultiply defMultiply)
        {
            UnhandledNodeType("DefMultiply");
        }

        public virtual void Visit(AmlParser.DefNAnd defNAnd)
        {
            UnhandledNodeType("DefNAnd");
        }

        public virtual void Visit(AmlParser.DefNOr defNOr)
        {
            UnhandledNodeType("DefNOr");
        }

        public virtual void Visit(AmlParser.DefNot defNot)
        {
            UnhandledNodeType("DefNot");
        }

        public virtual void Visit(AmlParser.DefObjectType defObjectType)
        {
            UnhandledNodeType("DefObjectType");
        }

        public virtual void Visit(AmlParser.DefOr defOr)
        {
            UnhandledNodeType("DefOr");
        }

        public virtual void Visit(AmlParser.DefPackage defPackage)
        {
            UnhandledNodeType("DefPackage");
        }

        public virtual void Visit(AmlParser.DefVarPackage defVarPackage)
        {
            UnhandledNodeType("DefVarPackage");
        }

        public virtual void Visit(AmlParser.NumElements numElements)
        {
            UnhandledNodeType("NumElements");
        }

        public virtual void Visit(AmlParser.VarNumElements varNumElements)
        {
            UnhandledNodeType("VarNumElements");
        }

        public virtual void Visit(AmlParser.DefRefOf defRefOf)
        {
            UnhandledNodeType("DefRefOf");
        }

        public virtual void Visit(AmlParser.DefShiftLeft defShiftLeft)
        {
            UnhandledNodeType("DefShiftLeft");
        }

        public virtual void Visit(AmlParser.ShiftCount shiftCount)
        {
            UnhandledNodeType("ShiftCount");
        }

        public virtual void Visit(AmlParser.DefShiftRight defShiftRight)
        {
            UnhandledNodeType("DefShiftRight");
        }

        public virtual void Visit(AmlParser.DefSizeOf defSizeOf)
        {
            UnhandledNodeType("DefSizeOf");
        }

        public virtual void Visit(AmlParser.DefStore defStore)
        {
            UnhandledNodeType("DefStore");
        }

        public virtual void Visit(AmlParser.DefSubtract defSubtract)
        {
            UnhandledNodeType("DefSubtract");
        }

        public virtual void Visit(AmlParser.DefTimer defTimer)
        {
            UnhandledNodeType("DefTimer");
        }

        public virtual void Visit(AmlParser.DefToBCD defToBCD)
        {
            UnhandledNodeType("DefToBCD");
        }

        public virtual void Visit(AmlParser.DefToBuffer defToBuffer)
        {
            UnhandledNodeType("DefToBuffer");
        }

        public virtual void Visit(AmlParser.DefToDecimalString defToDecimalString)
        {
            UnhandledNodeType("DefToDecimalString");
        }

        public virtual void Visit(AmlParser.DefToHexString defToHexString)
        {
            UnhandledNodeType("DefToHexString");
        }

        public virtual void Visit(AmlParser.DefToInteger defToInteger)
        {
            UnhandledNodeType("DefToInteger");
        }

        public virtual void Visit(AmlParser.DefToString defToString)
        {
            UnhandledNodeType("DefToString");
        }

        public virtual void Visit(AmlParser.LengthArg lengthArg)
        {
            UnhandledNodeType("LengthArg");
        }

        public virtual void Visit(AmlParser.DefWait defWait)
        {
            UnhandledNodeType("DefWait");
        }

        public virtual void Visit(AmlParser.DefXOr defXOr)
        {
            UnhandledNodeType("DefXOr");
        }

        public virtual void Visit(AmlParser.ArgObj argObj)
        {
            UnhandledNodeType("ArgObj");
        }

        public virtual void Visit(AmlParser.LocalObj localObj)
        {
            UnhandledNodeType("LocalObj");
        }

        public virtual void Visit(AmlParser.DebugObj debugObj)
        {
            UnhandledNodeType("DebugObj");
        }
    }
}
