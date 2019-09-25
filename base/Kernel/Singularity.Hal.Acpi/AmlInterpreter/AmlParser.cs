///////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Microsoft Research Singularity
//

//#define DEBUG_AML_PARSER

using System.Collections;
using System.Diagnostics;
using System.Text;

using AccessType = Microsoft.Singularity.Hal.Acpi.AcpiObject.AccessType;
using AccessAttrib = Microsoft.Singularity.Hal.Acpi.AcpiObject.AccessAttrib;
using LockRule = Microsoft.Singularity.Hal.Acpi.AcpiObject.LockRule;
using UpdateRule = Microsoft.Singularity.Hal.Acpi.AcpiObject.UpdateRule;
using SerializeFlag = Microsoft.Singularity.Hal.Acpi.AcpiObject.SerializeFlag;
using AbsoluteNodePath = Microsoft.Singularity.Hal.Acpi.AcpiNamespace.AbsoluteNodePath;

using Microsoft.Singularity.Hal.Acpi.AmlParserUnions;

// TODO list:
// * Better error handling. Currently just returns Failure if it fails to parse.

// This file implements a simple recursive descent parser based
// directly on the ACPI specification, Revision 3.0b, section 18.2, in
// order to ensure maximum compliance. Compile-time inlining and
// tail-recursion elimination should make it relatively efficient
// considering the simplicity of the grammar; for this reason, and
// because of annoying snags like the sub-byte encoding of package
// length, I opted for this implementation instead of using a
// full-blown parser generator like netcc on Toolbox.

// Most rules are taken directly from the spec. I made casing
// consistent and renamed the nonterminals "String" and "Object" to
// avoid keyword conflict, and changed some rules where indicated to
// make the grammar unambiguous and sensible.

// Note that in some cases identifiers are inconsistent with established
// naming conventions like "AMLCode" instead of "AmlCode". This is for
// consistency with the specification.

namespace Microsoft.Singularity.Hal.Acpi
{
    // Terminology used by ACPI spec for basic integer types (from section 18.2.3):
    // 
    // ByteData             := 0x00 - 0xFF
    // WordData             := ByteData[0:7] ByteData[8:15]
    //                         // 0x0000-0xFFFF
    // DWordData            := WordData[0:15] WordData[16:31]
    //                         // 0x00000000-0xFFFFFFFF
    // QWordData            := DWordData[0:31] DWordData[32:63]
    //                         // 0x0000000000000000-0xFFFFFFFFFFFFFFFF

    using ByteData  = System.Byte;
    using WordData  = System.UInt16;
    using DWordData = System.UInt32;
    using QWordData = System.UInt64;

    // This interface defines a basic read-only stream interface for the
    // AML parser input that is sufficient for the purposes of the parser.
    // Any attempt to read past the end of the stream produces the exception
    // EndOfAmlStreamException.
    public interface IAmlStream
    {
        // Read 8-bit byte at the given offset, updating the offset past it
        ByteData ReadByteData(ref int offset);

        // Try to read 8-bit byte at the given offset, updating the offset past it,
        // and returning false and not updating offset if offset is at end of stream.
        bool TryReadByteData(ref int offset, out ByteData result);

        // Read 8-bit byte at the given offset as a character, updating the offset past it
        char ReadChar(ref int offset);

        // Reads "length" 8-bit bytes at the given offset, updating the offset past them
        ByteData[] ReadByteDataArray(ref int offset, int length);

        // Reads "length" 8-bit bytes at the given offset, updating the offset past them,
        // and returning false and not updating offset if offset is at end of stream.
        bool TryReadByteDataArray(ref int offset, int length, out ByteData[] result);

        // Read 16-bit word at the given offset, updating the offset past it
        WordData ReadWordData(ref int offset);

        // Read 32-bit word at the given offset, updating the offset past it
        DWordData ReadDWordData(ref int offset);

        // Read 64-bit word at the given offset, updating the offset past it
        QWordData ReadQWordData(ref int offset);
    }

    public class EndOfAmlStreamException : System.Exception
    {
    }

    public class AmlMalformattedException : System.Exception
    {
        public AmlMalformattedException()
            : base("Malformatted AML") { }

        public AmlMalformattedException(string reason)
          : base("Malformatted AML: " + reason) { }
    }

    // Base parser node class
    public abstract class AmlParserNode
    {
        public abstract void Accept(AmlParserNodeVisitor v);
    }

#if !SINGULARITY_KERNEL
    public class Debug
    {
        public static void Assert(bool b)
        {
            if (!b) {
                throw new System.Exception("Failed assertion");
            }
        }

        public static void Assert(bool b, string s)
        {
            if (!b) {
                throw new System.Exception("Failed assertion");
            }
        }
    }
#endif

    // Main parser class
    public class AmlParser
    {
        private IAmlStream stream;
        private IDictionary methodNumArgsByName = new SortedList();
        private AcpiNamespace acpiNamespace;
        private AcpiNamespace.AbsoluteNodePath currentNodePath;

        public AmlParser(IAmlStream stream, AcpiNamespace acpiNamespace,
                         AcpiNamespace.AbsoluteNodePath initialNodePath)
        {
            this.stream = stream;
            this.acpiNamespace = acpiNamespace;
            this.currentNodePath = initialNodePath;
        }

        public enum ParseSuccess
        {
            Success,
            Failure
        }
        const ParseSuccess Success = ParseSuccess.Success;
        const ParseSuccess Failure = ParseSuccess.Failure;

        private void VerifyFormat(bool condition, string malformattedReason)
        {
            if (!condition) {
                throw new AmlMalformattedException(malformattedReason);
            }
        }

        //
        // Section 18.2: AML Grammar Definition
        //

        // This section defines the byte values that make up an AML byte stream.
        // The AML encoding can be categorized in the following groups:
        //     * Table and Table Header encoding
        //     * Name objects encoding
        //     * Data objects encoding
        //     * Package length encoding
        //     * Term objects encoding
        //     * Miscellaneous objects encoding

        //
        // Section 18.2.1: Table and Table Header Encoding
        //

        // AMLCode              := DefBlockHdr TermList
        //[DefBlockHdr is handled by SystemTableHeader under Kernel\Singulary.Acpi, so
        // we just make this top-level rule contain a TermList.]

        public class AMLCode : AmlParserNode
        {
            public TermObj[] termList;

            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        // Main entry point
        public ParseSuccess ParseAMLCode(out AMLCode result, ref int offset, int endOffset)
        {
            int offset2 = offset;
            result = new AMLCode();
            if (ParseTermList(out result.termList, ref offset2, endOffset) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // DefBlockHdr          := TableSignature TableLength SpecCompliance CheckSum OemID
        //                         OemTableID OemRevision CreatorID CreatorRevision
        //[Handled by SystemTableHeader under Kernel\Singulary.Acpi ]

        // TableSignature       := DWordData // As defined in section 5.2.3.
        // TableLength          := DWordData // Length of the table in bytes including
        //                                   // the block header.
        // SpecCompliance       := ByteData // The revision of the structure.
        // CheckSum             := ByteData // Byte checksum of the entire table.
        // OemID                := ByteData(6) // OEM ID of up to 6 characters. If the OEM
        //                                     // ID is shorter than 6 characters, it
        //                                     // can be terminated with a NULL
        //                                     // character.
        // OemTableID           := ByteData(8) // OEM Table ID of up to 8 characters. If
                                               // the OEM Table ID is shorter than 8
                                               // characters, it can be terminated with
                                               // a NULL character.
        // OemRevision          := DWordData // OEM Table Revision.
        // CreatorID            := DWordData // Vendor ID of the ASL compiler.
        // CreatorRevision      := DWordData // Revision of the ASL compiler.

        //
        // Section 18.2.2: Name Objects Encoding
        //

        // [These rules just constrain the characters in NameSegs,
        //  already described by assertions in AcpiNamespace.AssertIsValidName().
        // LeadNameChar         := 'A'-'Z' | '_'
        // DigitChar            := '0'-'9'
        // NameChar             := DigitChar | LeadNameChar

        // RootChar             := '\'

        private bool IsRootChar(char data)
        {
            return data == (byte)'\\';
        }
        
        private ParseSuccess ParseRootChar(ref int offset)
        {
            int offset2 = offset;
            char c = stream.ReadChar(ref offset2);
            if (!IsRootChar(c)) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // ParentPrefixChar     := '^'

        private bool IsParentPrefixChar(char data)
        {
            return data == (byte)'^';
        }
        
        private ParseSuccess ParseParentPrefixChar(ref int offset)
        {
            int offset2 = offset;
            char c = stream.ReadChar(ref offset2);
            if (!IsParentPrefixChar(c)) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // NameSeg              := <LeadNameChar NameChar NameChar NameChar>
        //                         // Notice that NameSegs shorter than 4 characters
        //                         // are filled with trailing underscores ('_'s).

        public class NameSeg : AmlParserNode
        {
            public string data;

            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private char[] nameCharsTemp = new char[4];

        private ParseSuccess ParseNameSeg(out NameSeg result, ref int offset)
        {
            int offset2 = offset;
            result = null;

            // First check first character to avoid spurious allocations
            char firstChar = stream.ReadChar(ref offset2);
            if (!(System.Char.IsUpper(firstChar) || firstChar == '_')) {
                return Failure;
            }

            offset2 = offset; // Rewind to first character
            byte[] nameBytes;
            if (!stream.TryReadByteDataArray(ref offset2, 4, out nameBytes)) {
                return Failure;
            }

            if (!AcpiNamespace.IsValidName(nameBytes)) {
                return Failure;
            }

            for (int i = 0; i < nameCharsTemp.Length; i++) {
                nameCharsTemp[i] = (char)nameBytes[i];
            }
            string name = new string(nameCharsTemp);

            result = new NameSeg();
            result.data = name;

            offset = offset2;
            return Success;
        }

        // NameString           := <RootChar NamePath> | <PrefixPath NamePath>

        public class NameString : AmlParserNode
        {
            public AcpiNamespace.NodePath nodePath;

            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private string[] NamePathToStringArray(NamePath namePath)
        {
            string[] result = new string[namePath.segments.Length];
            for(int i = 0; i < result.Length; i++) {
                result[i] = namePath.segments[i].data;
            }
            return result;
        }

        private ParseSuccess ParseNameString(out NameString result, ref int offset)
        {
            result = null;
            int offset2 = offset;

            if (ParseRootChar(ref offset2) == Success) {
                NamePath namePath;
                if (ParseNamePath(out namePath, ref offset2) == Failure) {
                    return Failure;
                }
                result = new NameString();
                result.nodePath = new AcpiNamespace.NodePath(true/*isAbsolute*/, 0, NamePathToStringArray(namePath));
            }
            else {
                PrefixPath prefixPath;
                NamePath namePath;
                if (ParsePrefixPath(out prefixPath, ref offset2) == Failure ||
                    ParseNamePath(out namePath, ref offset2) == Failure) {
                    return Failure;
                }
                result = new NameString();
                result.nodePath = new AcpiNamespace.NodePath(false/*isAbsolute*/, prefixPath.length, NamePathToStringArray(namePath));
            }

            offset = offset2;
            return Success;
        }

        // PrefixPath           := Nothing | <'^' PrefixPath>
        // [I use ParentPrefixChar (otherwise unused) for '^']

        public class PrefixPath : AmlParserNode
        {
            public int length;

            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParsePrefixPath(out PrefixPath result, ref int offset)
        {
            int offset2 = offset;
            result = new PrefixPath();
            result.length = 0;
            while (ParseParentPrefixChar(ref offset2) != Failure) {
                result.length++;
            }
            offset = offset2;
            return Success;
        }

        // NamePath             := NameSeg | DualNamePath | MultiNamePath | NullName

        public class NamePath : AmlParserNode
        {
            public NameSeg[] segments;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseNamePath(out NamePath result, ref int offset)
        {
            int offset2 = offset;
            result = new NamePath();

            if (ParseDualNamePath(out result.segments, ref offset2) == Failure &&
                ParseMultiNamePath(out result.segments, ref offset2) == Failure &&
                ParseNullName(out result.segments, ref offset2)      == Failure) {
                result.segments = new NameSeg[1];
                if (ParseNameSeg(out result.segments[0], ref offset2) == Failure) {
                    return Failure;
                }
            }

            offset = offset2;
            return Success;
        }

        // DualNamePath         := DualNamePrefix NameSeg NameSeg

        private ParseSuccess ParseDualNamePath(out NameSeg[] result, ref int offset)
        {
            int offset2 = offset;
            result = null;

            char prefix = stream.ReadChar(ref offset2);
            if (prefix != DualNamePrefix) {
                return Failure;
            }

            result = new NameSeg[2];
            if (ParseNameSeg(out result[0], ref offset2) == Failure ||
                ParseNameSeg(out result[1], ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DualNamePrefix       := 0x2E

        private const char DualNamePrefix = '\x002E';

        // MultiNamePath        := MultiNamePrefix SegCount NameSeg(SegCount)

        private ParseSuccess ParseMultiNamePath(out NameSeg[] result, ref int offset)
        {
            int offset2 = offset;
            result = null;

            char prefix = stream.ReadChar(ref offset2);
            if (prefix != MultiNamePrefix) {
                return Failure;
            }

            SegCount segCount;
            if (ParseSegCount(out segCount, ref offset2) == Failure) {
                return Failure;
            }
            result = new NameSeg[segCount.data];
            for (int segNum = 0; segNum < segCount.data; segNum++) {
                if (ParseNameSeg(out result[segNum], ref offset2) == Failure) {
                    return Failure;
                }
            }

            offset = offset2;
            return Success;
        }

        // MultiNamePrefix      := 0x2F

        private const char MultiNamePrefix = '\x002F';

        // SegCount             := ByteData
        // Note: SegCount can be from 1 to 255. For example:
        // MultiNamePrefix(35) is encoded as 0x2f 0x23 and followed by
        // 35 NameSegs. So, the total encoding length will be 1 + 1 +
        // 35*4 = 142. Notice that: DualNamePrefix NameSeg NameSeg has
        // a smaller encoding than the encoding of: MultiNamePrefix(2)
        // NameSeg NameSeg

        public class SegCount : AmlParserNode
        {
            public ByteData data;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseSegCount(out SegCount result, ref int offset)
        {
            int offset2 = offset;
            result = new SegCount();
            result.data = stream.ReadByteData(ref offset2);
            offset = offset2;
            return Success;
        }

        // SimpleName           := NameString | ArgObj | LocalObj
        // See AmlParser.csunion

        private ParseSuccess ParseSimpleName(out SimpleName result, ref int offset)
        {
            int offset2 = offset;

            NameString nameString;
            ArgObj argObj;
            LocalObj localObj;
            if (ParseArgObj(out argObj, ref offset2) == Success) {
                result = SimpleName.CreateArgObj(argObj);
            }
            else if (ParseLocalObj(out localObj, ref offset2) == Success) {
                result = SimpleName.CreateLocalObj(localObj);
            }
            else if (ParseNameString(out nameString, ref offset2) == Success) {
                result = SimpleName.CreateNameString(nameString);
            } 
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // SuperName            := SimpleName | DebugObj | Type6Opcode
        // See AmlParser.csunion

        private ParseSuccess ParseSuperName(out SuperName result, ref int offset)
        {
            int offset2 = offset;

            // There's an ambiguity here! What to do?
            //    SuperName -> SimpleName -> NameString
            //    SuperName -> Type6Opcode -> UserTermObj
            //              -> NameString TermArgList -> NameString
            // For now just doing whatever the parser chooses first.
            SimpleName simpleName;
            DebugObj debugObj;
            Type6Opcode type6Opcode;
            if (ParseSimpleName(out simpleName, ref offset2) == Success) {
                result = SuperName.CreateSimpleName(simpleName);
            }
            else if (ParseDebugObj(out debugObj, ref offset2) == Success) {
                result = SuperName.CreateDebugObj(debugObj);
            }
            else if (ParseType6Opcode(out type6Opcode, ref offset2) == Success) {
                result = SuperName.CreateType6Opcode(type6Opcode);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // NullName             := 0x00

        private ParseSuccess ParseNullName(out NameSeg[] result, ref int offset)
        {
            int offset2 = offset;
            result = null;

            char prefix = stream.ReadChar(ref offset2);
            if (prefix != '\0') {
                return Failure;
            }

            result = new NameSeg[0];
            offset = offset2;
            return Success;
        }

        // Target               := SuperName | NullName
        // [NOTE: SuperName can reduce to NullName anyway:
        //  SuperName -> SimpleName -> NameString -> PrefixPath NamePath
        //            -> NamePath -> NullName
        //  Therefore Target is the same thing as SuperName. We wrap it
        //  for type safety only.]

        public class Target : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseTarget(out Target result, ref int offset)
        {
            int offset2 = offset;
            result = new Target();
            if (ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        //
        // Section 18.2.3: Data Objects Encoding
        //

        // ComputationalData    := ByteConst | WordConst | DWordConst | QWordConst |
        //                         StringConst | ConstObj | RevisionOp | DefBuffer
        // See AmlParser.csunion

        private ParseSuccess ParseComputationalData(out ComputationalData result, ref int offset)
        {
            int offset2 = offset;

            ByteData byteConst;
            WordData wordConst;
            DWordData dWordConst;
            QWordData qWordConst;
            string stringConst;
            ConstObj constObj;
            DefBuffer defBuffer;
            if (ParseByteConst(out byteConst, ref offset2) == Success) {
                result = ComputationalData.CreateByteConst(byteConst);
            }
            else if (ParseWordConst(out wordConst, ref offset2) == Success) {
                result = ComputationalData.CreateWordConst(wordConst);
            }
            else if (ParseDWordConst(out dWordConst, ref offset2) == Success) {
                result = ComputationalData.CreateDWordConst(dWordConst);
            }
            else if (ParseQWordConst(out qWordConst, ref offset2) == Success) {
                result = ComputationalData.CreateQWordConst(qWordConst);
            }
            else if (ParseStringConst(out stringConst, ref offset2) == Success) {
                result = ComputationalData.CreateStringConst(stringConst);
            }
            else if (ParseConstObj(out constObj, ref offset2) == Success) {
                result = ComputationalData.CreateConstObj(constObj);
            }
            else if (ParseRevisionOp(ref offset2) == Success) {
                result = ComputationalData.CreateRevisionOp();
            }
            else if (ParseDefBuffer(out defBuffer, ref offset2) == Success) {
                result = ComputationalData.CreateDefBuffer(defBuffer);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DataObject           := ComputationalData | DefPackage | DefVarPackage
        // See AmlParser.csunion

        private ParseSuccess ParseDataObject(out DataObject result, ref int offset)
        {
            int offset2 = offset;

            ComputationalData computationalData;
            DefPackage defPackage;
            DefVarPackage defVarPackage;
            if (ParseDefPackage(out defPackage, ref offset2) == Success) {
                result = DataObject.CreateDefPackage(defPackage);
            }
            else if (ParseDefVarPackage(out defVarPackage, ref offset2) == Success) {
                result = DataObject.CreateDefVarPackage(defVarPackage);
            }
            else if (ParseComputationalData(out computationalData, ref offset2) == Success) {
                result = DataObject.CreateComputationalData(computationalData);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DataRefObject        := DataObject | ObjectReference | DDBHandle
        // [Note that here ObjectReference and DDBHandle do not have
        //  rules; the only reasonable interpretation is that they mean
        //  "TermArg => ObjectReference" and "DDBHandleObject".]
        // See AmlParser.csunion

        private ParseSuccess ParseDataRefObject(out DataRefObject result, ref int offset)
        {
            int offset2 = offset;

            DataObject dataObject;
            TermArg objectReference;
            DDBHandleObject ddbHandle;
            if (ParseDataObject(out dataObject, ref offset2) == Success) {
                result = DataRefObject.CreateDataObject(dataObject);
            }
            else if (ParseTermArg(out objectReference, ref offset2) == Success) {
                //if (!TermArgEvaluatesTo(objectReference, TermArgType.ObjectReference) {
                //  return Failure;
                //}   
                result = DataRefObject.CreateObjectReference(objectReference);
            }
            else if (ParseDDBHandleObject(out ddbHandle, ref offset2) == Success) {
                result = DataRefObject.CreateDDBHandle(ddbHandle);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // ByteConst            := BytePrefix ByteData

        private ParseSuccess ParseByteConst(out ByteData result, ref int offset)
        {
            int offset2 = offset;
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != BytePrefix) {
                result = 0;
                return Failure;
            }
            result = stream.ReadByteData(ref offset2);
            offset = offset2;
            return Success;
        }

        // BytePrefix           := 0x0A

        const ByteData BytePrefix = 0x0A;

        // WordConst            := WordPrefix WordData

        private ParseSuccess ParseWordConst(out WordData result, ref int offset)
        {
            int offset2 = offset;
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != WordPrefix) {
                result = 0;
                return Failure;
            }
            result = stream.ReadWordData(ref offset2);
            offset = offset2;
            return Success;
        }

        // WordPrefix           := 0x0B

        const ByteData WordPrefix = 0x0B;

        // DWordConst           := DWordPrefix DWordData

        private ParseSuccess ParseDWordConst(out DWordData result, ref int offset)
        {
            int offset2 = offset;
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != DWordPrefix) {
                result = 0;
                return Failure;
            }
            result = stream.ReadDWordData(ref offset2);
            offset = offset2;
            return Success;
        }

        // DWordPrefix          := 0x0C

        const ByteData DWordPrefix = 0x0C;

        // QWordConst           := QWordPrefix QWordData

        private ParseSuccess ParseQWordConst(out QWordData result, ref int offset)
        {
            int offset2 = offset;
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != QWordPrefix) {
                result = 0;
                return Failure;
            }
            result = stream.ReadQWordData(ref offset2);
            offset = offset2;
            return Success;
        }

        // QWordPrefix          := 0x0E

        const ByteData QWordPrefix = 0x0E;

        // StringConst          := StringPrefix AsciiCharList NullChar
        // AsciiCharList        := Nothing | <AsciiChar AsciiCharList>

        private ParseSuccess ParseStringConst(out string result, ref int offset)
        {
            int offset2 = offset;
            result = null;

            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != StringPrefix) {
                return Failure;
            }

            StringBuilder resultBuilder = new StringBuilder();
            while (true) {
                char c = stream.ReadChar(ref offset2);
                if (c == NullChar) {
                    break;
                }
                if (!IsAsciiChar(c)) {
                    return Failure;
                }
                resultBuilder.Append(c);
            }

            result = resultBuilder.ToString();
            offset = offset2;
            return Success;
        }

        // StringPrefix         := 0x0D

        const ByteData StringPrefix = 0x0D;

        // ConstObj             := ZeroOp | OneOp | OnesOp

        public class ConstObj : AmlParserNode
        {
            public ByteData op;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseConstObj(out ConstObj result, ref int offset)
        {
            int offset2 = offset;
            result = new ConstObj();
            ByteData op = stream.ReadByteData(ref offset2);
            if (op != ZeroOp &&
                op != OneOp  &&
                op != OnesOp) {
                return Failure;
            }
            result.op = op;
            offset = offset2;
            return Success;
        }

        // ByteList             := Nothing | <ByteData ByteList>
        // [To make this rule make sense, it needs a length
        //  limit for termination. The rule using it should know this.]

        private ParseSuccess ParseByteList(out ByteData[] result, ref int offset, int endOffset)
        {
            int offset2 = offset;
            result = stream.ReadByteDataArray(ref offset2, endOffset - offset);
            offset = offset2;
            return Success;
        }

        // AsciiChar            := 0x01 - 0x7F

        private bool IsAsciiChar(char data)
        {
            return (byte)data >= 0x01 && (byte)data <= 0x7F;
        }

        // NullChar             := 0x00

        char NullChar = '\0';

        // ZeroOp               := 0x00

        public const ByteData ZeroOp = 0x00;

        // OneOp                := 0x01

        public const ByteData OneOp = 0x01;

        // OnesOp               := 0xFF

        public const ByteData OnesOp = 0xFF;

        // RevisionOp           := ExtOpPrefix 0x30

        private ParseSuccess ParseRevisionOp(ref int offset)
        {
            int offset2 = offset;
            ByteData b = stream.ReadByteData(ref offset2);
            if (b != ExtOpPrefix) {
                return Failure;
            }
            b = stream.ReadByteData(ref offset2);
            if (b != 0x30) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // ExtOpPrefix          := 0x5B

        const ByteData ExtOpPrefix = 0x5B;

        //
        // Section 18.2.4: Package Length Encoding
        //

        // PkgLength            := PkgLeadByte |
        //                         <PkgLeadByte ByteData> |
        //                         <PkgLeadByte ByteData ByteData> |
        //                         <PkgLeadByte ByteData ByteData ByteData>

        // PkgLeadByte          := <bit 7-6: ByteData count that follows (0-3)>
        //                         <bit 5-4: Only used if PkgLength < 63>
        //                         <bit 3-0: Least significant package length nybble>

        // Note: The high 2 bits of the first byte reveal how many
        // follow bytes are in the PkgLength. If the PkgLength has
        // only one byte, bit 0 through 5 are used to encode the
        // package length (in other words, values 0-63). If the
        // package length value is more than 63, more than one byte
        // must be used for the encoding in which case bit 4 and 5 of
        // the PkgLeadByte are reserved and must be zero. If the
        // multiple bytes encoding is used, bits 0-3 of the
        // PkgLeadByte become the least significant 4 bits of the
        // resulting package length value. The next ByteData will
        // become the next least significant 8 bits of the resulting
        // value and so on, up to 3 ByteData bytes. Thus, the maximum
        // package length is 2**28.

        private ParseSuccess ParsePkgLength(out int result, ref int offset)
        {
            int offset2 = offset;
            int length = 0; // Maximum 2^31 - 1 >= 2^28

            ByteData pkgLeadByte = stream.ReadByteData(ref offset2);
            int followingByteDataCount = pkgLeadByte >> 6;
            if (followingByteDataCount == 0) {
                // Bits 5-0 contain package length
                length = pkgLeadByte & 0x3F;
            }
            else {
                VerifyFormat(((pkgLeadByte >> 4) & 3) == 0,
                             "Expect bits 5-4 zero when bits 7-6 nonzero in PkgLeadByte");
                length = pkgLeadByte & 0xF;
                int shiftAmount = 4;
                for (int i = 0; i < followingByteDataCount; i++) {
                    ByteData b = stream.ReadByteData(ref offset2);
                    length = length | (((int)b) << shiftAmount);
                    shiftAmount += 8;
                }
            }
            result = length;
            offset = offset2;
            return Success;
        }

        // [This wrapper converts a PkgLength result to a more useful
        //  position-independent end offset of the area measured by the
        //  PkgLength. This offset is exclusive (the byte at that offset
        //  is not itself in the area).]
        private ParseSuccess ParsePkgLengthEndOffset(out int endOffset, ref int offset)
        {
            int offset2 = offset;
            int length;
            if (ParsePkgLength(out length, ref offset2) == Failure) {
                endOffset = 0;
                return Failure;
            }
            endOffset = offset + length;
            offset = offset2;
            return Success;
        }
            
        //
        // Section 18.2.5: Term Objects Encoding
        //

        // TermObj              := NameSpaceModifierObj | NamedObj | Type1Opcode | Type2Opcode
        // See AmlParser.csunion

        private ParseSuccess ParseTermObj(out TermObj result, ref int offset, int endOffset)
        {
            int offset2 = offset;

            NameSpaceModifierObj nameSpaceModifierObj;
            NamedObj namedObj;
            Type1Opcode type1Opcode;
            Type2Opcode type2Opcode;
            if (ParseNamedObj(out namedObj, ref offset2) == Success) {
                result = TermObj.CreateNamedObj(namedObj);
            }
            else if (ParseType1Opcode(out type1Opcode, ref offset2, endOffset) == Success) {
                result = TermObj.CreateType1Opcode(type1Opcode);
            }
            else if (ParseType2Opcode(out type2Opcode, ref offset2) == Success) {
                result = TermObj.CreateType2Opcode(type2Opcode);
            }
            else if (ParseNameSpaceModifierObj(out nameSpaceModifierObj, ref offset2) == Success) {
                result = TermObj.CreateNameSpaceModifierObj(nameSpaceModifierObj);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // TermList             := Nothing | <TermObj TermList>
        // [To make this rule make sense, it needs a length
        //  limit for termination. The rule using it should know this.]

        private class TermList
        {
            ArrayList list = new ArrayList();

            public void Add(TermObj termObj)
            {
                list.Add(termObj);
            }

            public TermObj[] ToArray()
            {
                return (TermObj[])list.ToArray(typeof(TermObj));
            }
        }

        public ParseSuccess ParseTermList(out TermObj[] result, ref int offset, int endOffset)
        {
            result = null;
            TermList termObjs = new TermList();
            int offset2 = offset;

            while (offset2 < endOffset) {
#if DEBUG_AML_PARSER
                System.Console.WriteLine(offset2.ToString("x8"));
#endif
                TermObj termObj;
                if (ParseTermObj(out termObj, ref offset2, endOffset) == Failure) {
                    return Failure;
                }
                termObjs.Add(termObj);
            }
            Debug.Assert(offset2 == endOffset);
            
            result = termObjs.ToArray();
            offset = offset2;
            return Success;
        }

        // TermArg              := Type2Opcode | DataObject | ArgObj | LocalObj
        // See AmlParser.csunion

        private ParseSuccess ParseTermArg(out TermArg result, ref int offset)
        {
            int offset2 = offset;

            Type2Opcode type2Opcode;
            DataObject dataObject;
            ArgObj argObj;
            LocalObj localObj;
            // Type2Opcode must be tried after DataObject, because the constant object
            // Zero will otherwise parse as a UserTermObj with NullName for Namestring.
            if (ParseDataObject(out dataObject, ref offset2) == Success) {
                result = TermArg.CreateDataObject(dataObject);
            }
            else if (ParseArgObj(out argObj, ref offset2) == Success) {
                result = TermArg.CreateArgObj(argObj);
            }
            else if (ParseLocalObj(out localObj, ref offset2) == Success) {
                result = TermArg.CreateLocalObj(localObj);
            }
            else if (ParseType2Opcode(out type2Opcode, ref offset2) == Success) {
                result = TermArg.CreateType2Opcode(type2Opcode);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // UserTermObj          := NameString TermArgList
        // [This rule annoyingly uses a variable-length list that, unlike every other
        //  such list, is determined not by an obvious encoded PkgLength. According to the engineer
        //  who worked on the Windows AML parser, it's necessary to look up the method indicated
        //  by the NameString to determine its number of arguments. To accomplish this we delay
        //  parsing of the method body until after all methods have been loaded into the namespace.]

        public class UserTermObj : AmlParserNode
        {
            public NameString nameString;
            public TermArg[] termArgList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseUserTermObj(out UserTermObj result, ref int offset)
        {
            int offset2 = offset;
            result = new UserTermObj();

            if (ParseNameString (out result.nameString, ref offset2) == Failure) {
                return Failure;
            }

            int numTermArgs = 0;
            AcpiNamespace.Node node = null;
            if (acpiNamespace != null) {
                node = acpiNamespace.LookupNode(result.nameString.nodePath, currentNodePath);
            }
            if (node != null && node.Value is AcpiObject.Method) {
                numTermArgs = ((AcpiObject.Method)node.Value).ArgCount;
            }
            else {
                numTermArgs = 0; // If we're still loading, it can't be a method call, must have zero args
            }

            if (ParseTermArgListN(out result.termArgList, ref offset2, numTermArgs) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // TermArgList          := Nothing | <TermArg TermArgList>
        // [To make this rule make sense, it needs a length
        //  limit for termination. The rule using it should know this.]

        private class TermArgList
        {
            ArrayList list = new ArrayList();

            public void Add(TermArg termArg)
            {
                list.Add(termArg);
            }

            public TermArg[] ToArray()
            {
                return (TermArg[])list.ToArray(typeof(TermArg));
            }
        }

        private ParseSuccess ParseTermArgList(out TermArg[] result, ref int offset, int endOffset)
        {
            result = null;
            TermArgList termArgs = new TermArgList();
            int offset2 = offset;

            while (offset2 < endOffset) {
                TermArg termArg;
                if (ParseTermArg(out termArg, ref offset2) == Failure) {
                    return Failure;
                }
                termArgs.Add(termArg);
            }
            Debug.Assert(offset2 == endOffset);
            
            result = termArgs.ToArray();
            offset = offset2;
            return Success;
        }

        // For UserTermObj rule, parses a specified number of TermArgs
        private ParseSuccess ParseTermArgListN(out TermArg[] result, ref int offset, int numTermArgs)
        {
            int offset2 = offset;
            result = new TermArg[numTermArgs];

            for (int i = 0; i < numTermArgs; i++) {
                if (ParseTermArg(out result[i], ref offset2) == Failure) {
                    return Failure;
                }
            }
           
            offset = offset2;
            return Success;
        }

        // AmlObjectList           := Nothing | <AmlObject AmlObjectList>
        // [To make this rule make sense, it needs a length
        //  limit for termination. The rule using it should know this.]

        private class AmlObjectList
        {
            ArrayList list = new ArrayList();

            public void Add(AmlObject amlObject)
            {
                list.Add(amlObject);
            }

            public AmlObject[] ToArray()
            {
                return (AmlObject[])list.ToArray(typeof(AmlObject));
            }
        }

        private ParseSuccess ParseAmlObjectList(out AmlObject[] result, ref int offset, int endOffset)
        {
            result = null;
            AmlObjectList amlObjects = new AmlObjectList();
            int offset2 = offset;

            while (offset2 < endOffset) {
                AmlObject amlObject;
                if (ParseAmlObject(out amlObject, ref offset2) == Failure) {
                    return Failure;
                }
                amlObjects.Add(amlObject);
            }
            Debug.Assert(offset2 == endOffset);
            
            result = amlObjects.ToArray();
            offset = offset2;
            return Success;
        }

        // AmlObject               := NameSpaceModifierObj | NamedObj
        // See AmlParser.csunion

        private ParseSuccess ParseAmlObject(out AmlObject result, ref int offset)
        {
            int offset2 = offset;

            NameSpaceModifierObj nameSpaceModifierObj;
            NamedObj namedObj;
            if (ParseNameSpaceModifierObj(out nameSpaceModifierObj, ref offset2) == Success) {
                result = AmlObject.CreateNameSpaceModifierObj(nameSpaceModifierObj);
            }
            else if (ParseNamedObj(out namedObj, ref offset2) == Success) {
                result = AmlObject.CreateNamedObj(namedObj);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        //
        // Section 18.2.5.1: Namespace Modifier Objects Encoding
        //

        // NameSpaceModifierObj := DefAlias | DefName | DefScope
        // See AmlParser.csunion

        private ParseSuccess ParseNameSpaceModifierObj(out NameSpaceModifierObj result, ref int offset)
        {
            int offset2 = offset;

            DefAlias defAlias;
            DefName defName;
            DefScope defScope;
            if (ParseDefAlias(out defAlias, ref offset2) == Success) {
                result = NameSpaceModifierObj.CreateDefAlias(defAlias);
            }
            else if (ParseDefName(out defName, ref offset2) == Success) {
                result = NameSpaceModifierObj.CreateDefName(defName);
            }
            else if (ParseDefScope(out defScope, ref offset2) == Success) {
                result = NameSpaceModifierObj.CreateDefScope(defScope);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefAlias             := AliasOp NameString NameString

        public class DefAlias : AmlParserNode
        {
            public NameString sourceName;
            public NameString aliasName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefAlias(out DefAlias result, ref int offset)
        {
            int offset2 = offset;
            result = new DefAlias();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != AliasOp) {
                return Failure;
            }
            if (ParseNameString(out result.sourceName, ref offset2) == Failure ||
                ParseNameString(out result.aliasName, ref offset2)  == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // AliasOp              := 0x06

        const ByteData AliasOp = 0x06;
        
        // DefName              := NameOp NameString DataRefObject
        // [There is no DataRefObject rule. I assume they mean TermArg => DataRefObject as
        //  in the ArgObject rule.]

        public class DefName : AmlParserNode
        {
            public NameString nameString;
            public TermArg dataRefObject;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefName(out DefName result, ref int offset)
        {
            int offset2 = offset;
            result = new DefName();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != NameOp) {
                return Failure;
            }
            if (ParseNameString(out result.nameString, ref offset2) == Failure ||
                ParseTermArg(out result.dataRefObject, ref offset2)  == Failure /*||
                !TermArgEvaluatesTo(result.dataRefObject, TermArgType.DataRefObject*/) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // NameOp               := 0x08

        const ByteData NameOp = 0x08;
        
        // DefScope             := ScopeOp PkgLength NameString TermList

        public class DefScope : AmlParserNode
        {
            public NameString nameString;
            public TermObj[] termList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefScope(out DefScope result, ref int offset)
        {
            int offset2 = offset;
            result = new DefScope();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ScopeOp) {
                return Failure;
            }

            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseNameString(out result.nameString, ref offset2) == Failure) {
                return Failure;
            }

            AbsoluteNodePath oldNodePath = currentNodePath;
            if (acpiNamespace != null) {
                currentNodePath = acpiNamespace.LookupNode(result.nameString.nodePath, currentNodePath).Path;
            }
            if (ParseTermList(out result.termList, ref offset2, endOffset)  == Failure) {
                return Failure;
            }
            currentNodePath = oldNodePath;

            offset = offset2;
            return Success;
        }

        // ScopeOp              := 0x10

        const ByteData ScopeOp = 0x10;

        //
        // Section 18.2.5.2: Named Objects Encoding
        //

        // NamedObj             := DefBankField | DefCreateBitField | DefCreateByteField |
        //                         DefCreateDWordField | DefCreateField |
        //                         DefCreateQWordField | DefCreateWordField |
        //                         DefDataRegion | DefDevice | DefEvent | DefField |
        //                         DefIndexField | DefMethod | DefMutex | DefOpRegion |
        //                         DefPowerRes | DefProcessor | DefThermalZone
        // See AmlParser.csunion

        private ParseSuccess ParseNamedObj(out NamedObj result, ref int offset)
        {
            int offset2 = offset;

            DefBankField defBankField;
            DefCreateBitField defCreateBitField;
            DefCreateByteField defCreateByteField;
            DefCreateDWordField defCreateDWordField;
            DefCreateField defCreateField;
            DefCreateQWordField defCreateQWordField;
            DefCreateWordField defCreateWordField;
            DefDataRegion defDataRegion;
            DefDevice defDevice;
            DefEvent defEvent;
            DefField defField;
            DefIndexField defIndexField;
            DefMethod defMethod;
            DefMutex defMutex;
            DefOpRegion defOpRegion;
            DefPowerRes defPowerRes;
            DefProcessor defProcessor;
            DefThermalZone defThermalZone;
            if (ParseDefBankField(out defBankField, ref offset2) == Success ) {
                result = NamedObj.CreateDefBankField(defBankField);
            }
            else if (ParseDefCreateBitField(out defCreateBitField, ref offset2) == Success ) {
                result = NamedObj.CreateDefCreateBitField(defCreateBitField);
            }
            else if (ParseDefCreateByteField(out defCreateByteField, ref offset2) == Success ) {
                result = NamedObj.CreateDefCreateByteField(defCreateByteField);
            }
            else if (ParseDefCreateDWordField(out defCreateDWordField, ref offset2) == Success ) {
                result = NamedObj.CreateDefCreateDWordField(defCreateDWordField);
            }
            else if (ParseDefCreateField(out defCreateField, ref offset2) == Success ) {
                result = NamedObj.CreateDefCreateField(defCreateField);
            }
            else if (ParseDefCreateQWordField(out defCreateQWordField, ref offset2) == Success ) {
                result = NamedObj.CreateDefCreateQWordField(defCreateQWordField);
            }
            else if (ParseDefCreateWordField(out defCreateWordField, ref offset2) == Success ) {
                result = NamedObj.CreateDefCreateWordField(defCreateWordField);
            }
            else if (ParseDefDataRegion(out defDataRegion, ref offset2) == Success ) {
                result = NamedObj.CreateDefDataRegion(defDataRegion);
            }
            else if (ParseDefDevice(out defDevice, ref offset2) == Success ) {
                result = NamedObj.CreateDefDevice(defDevice);
            }
            else if (ParseDefEvent(out defEvent, ref offset2) == Success ) {
                result = NamedObj.CreateDefEvent(defEvent);
            }
            else if (ParseDefField(out defField, ref offset2) == Success ) {
                result = NamedObj.CreateDefField(defField);
            }
            else if (ParseDefIndexField(out defIndexField, ref offset2) == Success ) {
                result = NamedObj.CreateDefIndexField(defIndexField);
            }
            else if (ParseDefMethod(out defMethod, ref offset2) == Success ) {
                result = NamedObj.CreateDefMethod(defMethod);
            }
            else if (ParseDefMutex(out defMutex, ref offset2) == Success ) {
                result = NamedObj.CreateDefMutex(defMutex);
            }
            else if (ParseDefOpRegion(out defOpRegion, ref offset2) == Success ) {
                result = NamedObj.CreateDefOpRegion(defOpRegion);
            }
            else if (ParseDefPowerRes(out defPowerRes, ref offset2) == Success ) {
                result = NamedObj.CreateDefPowerRes(defPowerRes);
            }
            else if (ParseDefProcessor(out defProcessor, ref offset2) == Success ) {
                result = NamedObj.CreateDefProcessor(defProcessor);
            }
            else if (ParseDefThermalZone(out defThermalZone, ref offset2) == Success) {
                result = NamedObj.CreateDefThermalZone(defThermalZone);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefBankField         := BankFieldOp PkgLength NameString NameString BankValue FieldFlags FieldList

        public class DefBankField : AmlParserNode
        {
            public NameString regionName;
            public NameString bankName;
            public BankValue bankValue;
            public FieldFlags fieldFlags;
            public FieldElement[] fieldList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefBankField(out DefBankField result, ref int offset)
        {
            int offset2 = offset;
            result = new DefBankField();
            if (CheckTwoBytePrefix(BankFieldOp1, BankFieldOp2, ref offset2) == Failure) {
                return Failure;
            }

            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseNameString(out result.regionName, ref offset2) == Failure ||
                ParseNameString(out result.bankName, ref offset2)   == Failure ||
                ParseBankValue (out result.bankValue, ref offset2)  == Failure ||
                ParseFieldFlags(out result.fieldFlags, ref offset2) == Failure ||
                ParseFieldList (out result.fieldList, ref offset2, endOffset) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // BankFieldOp          := ExtOpPrefix 0x87

        const ByteData BankFieldOp1 = ExtOpPrefix;
        const ByteData BankFieldOp2 = 0x87;

        // BankValue            := TermArg => Integer

        public class BankValue : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseBankValue(out BankValue result, ref int offset)
        {
            int offset2 = offset;
            result = new BankValue();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // FieldFlags           := ByteData     // bit 0-3: AccessType
        //                                      //          0 AnyAcc
        //                                      //          1 ByteAcc
        //                                      //          2 WordAcc
        //                                      //          3 DWordAcc
        //                                      //          4 QWordAcc
        //                                      //          5 BufferAcc
        //                                      //          6 Reserved
        //                                      //          7-15 Reserved
        //                                      // bit 4: LockRule
        //                                      //          0 NoLock
        //                                      //          1 Lock
        //                                      // bit 5-6: UpdateRule
        //                                      //          0 Preserve
        //                                      //          1 WriteAsOnes
        //                                      //          2 WriteAsZeros
        //                                      // bit 7: Reserved (must be 0)

        public class FieldFlags : AmlParserNode
        {
            public AccessType accessType;
            public LockRule lockRule;
            public UpdateRule updateRule;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseFieldFlags(out FieldFlags result, ref int offset)
        {
            int offset2 = offset;
            result = new FieldFlags();

            ByteData b = stream.ReadByteData(ref offset2);

            result.accessType = (AccessType)(b & 0xF);
            result.lockRule   = (LockRule)((b >> 4) & 1);
            result.updateRule = (UpdateRule)((b >> 5) & 3);
            if (result.updateRule == UpdateRule.Invalid || ((b >> 7) != 0)) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // FieldList            := Nothing | <FieldElement FieldList>
        // [To make this rule make sense, it needs a length
        //  limit for termination. The rule using it should know this.]

        private class FieldList
        {
            ArrayList list = new ArrayList();

            public void Add(FieldElement fieldElement)
            {
                list.Add(fieldElement);
            }

            public FieldElement[] ToArray()
            {
                return (FieldElement[])list.ToArray(typeof(FieldElement));
            }
        }

        private ParseSuccess ParseFieldList(out FieldElement[] result, ref int offset, int endOffset)
        {
            result = null;
            FieldList fields = new FieldList();
            int offset2 = offset;

            while (offset2 < endOffset) {
                FieldElement fieldElement;
                if (ParseFieldElement(out fieldElement, ref offset2) == Failure) {
                    return Failure;
                }
                fields.Add(fieldElement);
            }
            Debug.Assert(offset2 == endOffset);
            
            result = fields.ToArray();
            offset = offset2;
            return Success;
        }

        // FieldElement         := NamedField | ReservedField | AccessField
        // See AmlParser.csunion

        private ParseSuccess ParseFieldElement(out FieldElement result, ref int offset)
        {
            int offset2 = offset;

            NamedField namedField;
            ReservedField reservedField;
            AccessField accessField;
            if (ParseNamedField(out namedField, ref offset2) == Success) {
                result = FieldElement.CreateNamedField(namedField);
            }
            else if (ParseReservedField(out reservedField, ref offset2) == Success) {
                result = FieldElement.CreateReservedField(reservedField);
            }
            else if (ParseAccessField(out accessField, ref offset2) == Success) {
                result = FieldElement.CreateAccessField(accessField);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // NamedField           := NameSeg PkgLength

        public class NamedField : AmlParserNode
        {
            public NameSeg nameSeg;
            public int bitWidth;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseNamedField(out NamedField result, ref int offset)
        {
            int offset2 = offset;
            result = new NamedField();

            if (ParseNameSeg  (out result.nameSeg,  ref offset2) == Failure ||
                ParsePkgLength(out result.bitWidth, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // ReservedField        := 0x00 PkgLength

        public class ReservedField : AmlParserNode
        {
            public int bitWidth;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseReservedField(out ReservedField result, ref int offset)
        {
            int offset2 = offset;
            result = new ReservedField();

            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != 0x00) {
                return Failure;
            }

            if (ParsePkgLength(out result.bitWidth, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // AccessField          := 0x01 AccessType AccessAttrib

        public class AccessField : AmlParserNode
        {
            public AccessType accessType;
            public AccessAttrib accessAttrib;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseAccessField(out AccessField result, ref int offset)
        {
            int offset2 = offset;
            result = new AccessField();

            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != 0x01) {
                return Failure;
            }

            if (ParseAccessType  (out result.accessType,  ref offset2) == Failure ||
                ParseAccessAttrib(out result.accessAttrib, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // AccessType           := ByteData     // Same as AccessType bits of FieldFlags.

        private ParseSuccess ParseAccessType(out AccessType result, ref int offset)
        {
            result = AccessType.AnyAcc;
            int offset2 = offset;

            ByteData b = stream.ReadByteData(ref offset2);
            if (b > 0xF) {
                return Failure;
            }
            result = (AccessType)b;

            offset = offset2;
            return Success;
        }

        // AccessAttrib         := ByteData     // If AccessType is BufferAcc for the SMB
        //                                      // OpRegion, AccessAttrib can be one of
        //                                      // the following values:
        //                                      //      0x02 SMBQuick
        //                                      //      0x04 SMBSendReceive
        //                                      //      0x06 SMBByte
        //                                      //      0x08 SMBWord
        //                                      //      0x0A SMBBlock
        //                                      //      0x0C SMBProcessCall
        //                                      //      0x0D SMBBlockProcessCall

        private ParseSuccess ParseAccessAttrib(out AcpiObject.AccessAttrib result, ref int offset)
        {
            result = AccessAttrib.SMBNone;
            int offset2 = offset;

            ByteData b = stream.ReadByteData(ref offset2);
            AccessAttrib type = (AccessAttrib)b;
            if (type != AccessAttrib.SMBNone &&
                type != AccessAttrib.SMBQuick &&
                type != AccessAttrib.SMBSendReceive &&
                type != AccessAttrib.SMBByte &&
                type != AccessAttrib.SMBWord &&
                type != AccessAttrib.SMBBlock &&
                type != AccessAttrib.SMBProcessCall &&
                type != AccessAttrib.SMBBlockProcessCall) {
                return Failure;
            }

            result = type;
            offset = offset2;
            return Success;
        }

        // DefCreateBitField    := CreateBitFieldOp SourceBuff BitIndex NameString

        public class DefCreateBitField : AmlParserNode
        {
            public SourceBuff sourceBuff;
            public BitIndex bitIndex;
            public NameString nameString;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefCreateBitField(out DefCreateBitField result, ref int offset)
        {
            int offset2 = offset;
            result = new DefCreateBitField();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != CreateBitFieldOp) {
                return Failure;
            }
            if (ParseSourceBuff(out result.sourceBuff, ref offset2) == Failure ||
                ParseBitIndex  (out result.bitIndex,   ref offset2) == Failure ||
                ParseNameString(out result.nameString, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // CreateBitFieldOp     := 0x8D

        const ByteData CreateBitFieldOp = 0x8D;

        // SourceBuff           := TermArg => Buffer

        public class SourceBuff : AmlParserNode
        {
            public TermArg buffer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseSourceBuff(out SourceBuff result, ref int offset)
        {
            int offset2 = offset;
            result = new SourceBuff();

            if (ParseTermArg(out result.buffer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.buffer, TermArgType.Buffer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // BitIndex             := TermArg => Integer

        public class BitIndex : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseBitIndex(out BitIndex result, ref int offset)
        {
            int offset2 = offset;
            result = new BitIndex();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefCreateByteField   := CreateByteFieldOp SourceBuff ByteIndex NameString

        public class DefCreateByteField : AmlParserNode
        {
            public SourceBuff sourceBuff;
            public ByteIndex byteIndex;
            public NameString nameString;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefCreateByteField(out DefCreateByteField result, ref int offset)
        {
            int offset2 = offset;
            result = new DefCreateByteField();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != CreateByteFieldOp) {
                return Failure;
            }
            if (ParseSourceBuff(out result.sourceBuff, ref offset2) == Failure ||
                ParseByteIndex (out result.byteIndex,  ref offset2) == Failure ||
                ParseNameString(out result.nameString, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // CreateByteFieldOp    := 0x8C

        const ByteData CreateByteFieldOp = 0x8C;

        // ByteIndex            := TermArg => Integer

        public class ByteIndex : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseByteIndex(out ByteIndex result, ref int offset)
        {
            int offset2 = offset;
            result = new ByteIndex();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefCreateDWordField  := CreateDWordFieldOp SourceBuff ByteIndex NameString

        public class DefCreateDWordField : AmlParserNode
        {
            public SourceBuff sourceBuff;
            public ByteIndex byteIndex;
            public NameString nameString;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefCreateDWordField(out DefCreateDWordField result, ref int offset)
        {
            int offset2 = offset;
            result = new DefCreateDWordField();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != CreateDWordFieldOp) {
                return Failure;
            }
            if (ParseSourceBuff(out result.sourceBuff, ref offset2) == Failure ||
                ParseByteIndex (out result.byteIndex,  ref offset2) == Failure ||
                ParseNameString(out result.nameString, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // CreateDWordFieldOp   := 0x8A

        const ByteData CreateDWordFieldOp = 0x8A;

        // DefCreateField       := CreateFieldOp SourceBuff BitIndex NumBits NameString

        public class DefCreateField : AmlParserNode
        {
            public SourceBuff sourceBuff;
            public BitIndex bitIndex;
            public NumBits numBits;
            public NameString nameString;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefCreateField(out DefCreateField result, ref int offset)
        {
            int offset2 = offset;
            result = new DefCreateField();

            if (CheckTwoBytePrefix(CreateFieldOp1, CreateFieldOp2, ref offset2) == Failure) {
                return Failure;
            }
            if (ParseSourceBuff(out result.sourceBuff, ref offset2) == Failure ||
                ParseBitIndex  (out result.bitIndex,   ref offset2) == Failure ||
                ParseNumBits   (out result.numBits,    ref offset2) == Failure ||
                ParseNameString(out result.nameString, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // CreateFieldOp        := ExtOpPrefix 0x13

        const ByteData CreateFieldOp1 = ExtOpPrefix;
        const ByteData CreateFieldOp2 = 0x13;

        // NumBits              := TermArg => Integer

        public class NumBits : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseNumBits(out NumBits result, ref int offset)
        {
            int offset2 = offset;
            result = new NumBits();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefCreateQWordField  := CreateQWordFieldOp SourceBuff ByteIndex NameString

        public class DefCreateQWordField : AmlParserNode
        {
            public SourceBuff sourceBuff;
            public ByteIndex byteIndex;
            public NameString nameString;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefCreateQWordField(out DefCreateQWordField result, ref int offset)
        {
            int offset2 = offset;
            result = new DefCreateQWordField();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != CreateQWordFieldOp) {
                return Failure;
            }
            if (ParseSourceBuff(out result.sourceBuff, ref offset2) == Failure ||
                ParseByteIndex (out result.byteIndex,  ref offset2) == Failure ||
                ParseNameString(out result.nameString, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // CreateQWordFieldOp   := 0x8F

        const ByteData CreateQWordFieldOp = 0x8F;

        // DefCreateWordField   := CreateWordFieldOp SourceBuff ByteIndex NameString

        public class DefCreateWordField : AmlParserNode
        {
            public SourceBuff sourceBuff;
            public ByteIndex byteIndex;
            public NameString nameString;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefCreateWordField(out DefCreateWordField result, ref int offset)
        {
            int offset2 = offset;
            result = new DefCreateWordField();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != CreateWordFieldOp) {
                return Failure;
            }
            if (ParseSourceBuff(out result.sourceBuff, ref offset2) == Failure ||
                ParseByteIndex (out result.byteIndex,  ref offset2) == Failure ||
                ParseNameString(out result.nameString, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // CreateWordFieldOp    := 0x8B

        const ByteData CreateWordFieldOp = 0x8B;

        // DefDataRegion        := DataRegionOp NameString TermArg TermArg TermArg

        public class DefDataRegion : AmlParserNode
        {
            public NameString nameString;
            public TermArg signatureString;
            public TermArg oemIDString;
            public TermArg oemTableIDString;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefDataRegion(out DefDataRegion result, ref int offset)
        {
            int offset2 = offset;
            result = new DefDataRegion();
            if (CheckTwoBytePrefix(DataRegionOp1, DataRegionOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseNameString(out result.nameString,      ref offset2) == Failure ||
                ParseTermArg   (out result.signatureString,  ref offset2) == Failure ||
                ParseTermArg   (out result.oemIDString,      ref offset2) == Failure ||
                ParseTermArg   (out result.oemTableIDString, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // DataRegionOp         := ExtOpPrefix 0x88

        const ByteData DataRegionOp1 = ExtOpPrefix;
        const ByteData DataRegionOp2 = 0x88;
        
        // DefDevice            := DeviceOp PkgLength NameString AmlObjectList

        public class DefDevice : AmlParserNode
        {
            public NameString nameString;
            public AmlObject[] amlObjectList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefDevice(out DefDevice result, ref int offset)
        {
            int offset2 = offset;
            result = new DefDevice();
            if (CheckTwoBytePrefix(DeviceOp1, DeviceOp2, ref offset2) == Failure) {
                return Failure;
            }

            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }
           
            if (ParseNameString   (out result.nameString,   ref offset2) == Failure) {
                return Failure;
            }

            AbsoluteNodePath oldNodePath = currentNodePath;
            if (acpiNamespace != null) {
                currentNodePath = acpiNamespace.LookupNode(result.nameString.nodePath, currentNodePath).Path;
            }
            if (ParseAmlObjectList(out result.amlObjectList, ref offset2, endOffset) == Failure) {
                return Failure;
            }
            currentNodePath = oldNodePath;

            offset = offset2;
            return Success;
        }
        
        // DeviceOp             := ExtOpPrefix 0x82

        const ByteData DeviceOp1 = ExtOpPrefix;
        const ByteData DeviceOp2 = 0x82;

        // DefEvent             := EventOp NameString

        public class DefEvent : AmlParserNode
        {
            public NameString nameString;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefEvent(out DefEvent result, ref int offset)
        {
            int offset2 = offset;
            result = new DefEvent();
            if (CheckTwoBytePrefix(EventOp1, EventOp2, ref offset2) == Failure) {
                return Failure;
            }
           
            if (ParseNameString(out result.nameString, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // EventOp              := ExtOpPrefix 0x02

        const ByteData EventOp1 = ExtOpPrefix;
        const ByteData EventOp2 = 0x02;

        // DefField             := FieldOp PkgLength NameString FieldFlags FieldList

        public class DefField : AmlParserNode
        {
            public NameString nameString;
            public FieldFlags fieldFlags;
            public FieldElement[] fieldList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefField(out DefField result, ref int offset)
        {
            int offset2 = offset;
            result = new DefField();
            if (CheckTwoBytePrefix(FieldOp1, FieldOp2, ref offset2) == Failure) {
                return Failure;
            }
           
            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }
           
            if (ParseNameString(out result.nameString, ref offset2) == Failure ||
                ParseFieldFlags(out result.fieldFlags, ref offset2) == Failure ||
                ParseFieldList (out result.fieldList,  ref offset2, endOffset) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // FieldOp              := ExtOpPrefix 0x81

        const ByteData FieldOp1 = ExtOpPrefix;
        const ByteData FieldOp2 = 0x81;

        // DefIndexField        := IndexFieldOp PkgLength NameString NameString FieldFlags FieldList
        
        public class DefIndexField : AmlParserNode
        {
            public NameString indexName;
            public NameString dataName;
            public FieldFlags fieldFlags;
            public FieldElement[] fieldList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefIndexField(out DefIndexField result, ref int offset)
        {
            int offset2 = offset;
            result = new DefIndexField();
            if (CheckTwoBytePrefix(IndexFieldOp1, IndexFieldOp2, ref offset2) == Failure) {
                return Failure;
            }
           
            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }
           
            if (ParseNameString(out result.indexName, ref offset2) == Failure ||
                ParseNameString(out result.dataName,   ref offset2) == Failure ||
                ParseFieldFlags(out result.fieldFlags, ref offset2) == Failure ||
                ParseFieldList (out result.fieldList,  ref offset2, endOffset) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // IndexFieldOp         := ExtOpPrefix 0x86

        const ByteData IndexFieldOp1 = ExtOpPrefix;
        const ByteData IndexFieldOp2 = 0x86;

        // DefMethod            := MethodOp PkgLength NameString MethodFlags TermList
        
        public class DefMethod : AmlParserNode
        {
            public NameString nameString;
            public MethodFlags methodFlags;
            public byte[] unparsedTermList;
            public TermObj[] termList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefMethod(out DefMethod result, ref int offset)
        {
            int offset2 = offset;
            result = null;
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != MethodOp) {
                return Failure;
            }
           
            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }

            NameString nameString;
            MethodFlags methodFlags;

            if (ParseNameString (out nameString, ref offset2) == Failure ||
                ParseMethodFlags(out methodFlags, ref offset2) == Failure) {
                return Failure;
            }

            result = new DefMethod();
            result.nameString = nameString;
            result.methodFlags = methodFlags;

            // We defer processing of the method body until later when all argument info is
            // known about methods that it might invoke.
            result.unparsedTermList = stream.ReadByteDataArray(ref offset2, endOffset - offset2);

            offset = offset2;
            return Success;
        }
        
        // MethodOp             := 0x14

        const ByteData MethodOp = 0x14;

        // MethodFlags          := ByteData       // bit 0-2:    ArgCount (0-7)
        //                                        // bit 3:      SerializeFlag
        //                                        //             0 NotSerialized
        //                                        //             1 Serialized
        //                                        // bit 4-7:    SyncLevel (0x00-0x0f)

        public class MethodFlags : AmlParserNode
        {
            public ByteData argCount;
            public SerializeFlag serializeFlag;
            public ByteData syncLevel;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseMethodFlags(out MethodFlags result, ref int offset)
        {
            int offset2 = offset;
            result = new MethodFlags();
            ByteData b = stream.ReadByteData(ref offset2);

            result.argCount = (byte)(b & 7);
            result.serializeFlag = (SerializeFlag)((b >> 3) & 1);
            result.syncLevel = (byte)(b >> 4);

            offset = offset2;
            return Success;
        }

        // DefMutex             := MutexOp NameString SyncFlags
        
        public class DefMutex : AmlParserNode
        {
            public NameString nameString;
            public SyncFlags syncFlags;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefMutex(out DefMutex result, ref int offset)
        {
            int offset2 = offset;
            result = new DefMutex();
            if (CheckTwoBytePrefix(MutexOp1, MutexOp2, ref offset2) == Failure) {
                return Failure;
            }
           
            if (ParseNameString(out result.nameString, ref offset2) == Failure ||
                ParseSyncFlags (out result.syncFlags,  ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // MutexOp              := ExtOpPrefix 0x01

        const ByteData MutexOp1 = ExtOpPrefix;
        const ByteData MutexOp2 = 0x01;

        // SyncFlags            := ByteData       // bit 0-3: SyncLevel (0x00-0x0f)
        //                                        // bit 4-7: Reserved (must be 0)

        public class SyncFlags : AmlParserNode
        {
            public ByteData syncLevel;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseSyncFlags(out SyncFlags result, ref int offset)
        {
            int offset2 = offset;
            result = new SyncFlags();
            ByteData b = stream.ReadByteData(ref offset2);

            if ((b >> 4) != 0) {
                return Failure;
            }
            result.syncLevel = (byte)(b & 0x0F);

            offset = offset2;
            return Success;
        }

        // DefOpRegion          := OpRegionOp NameString RegionSpace RegionOffset RegionLen
        
        public class DefOpRegion : AmlParserNode
        {
            public NameString   nameString;
            public RegionSpace  regionSpace;
            public RegionOffset regionOffset;
            public RegionLen    regionLen;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefOpRegion(out DefOpRegion result, ref int offset)
        {
            int offset2 = offset;
            result = new DefOpRegion();
            if (CheckTwoBytePrefix(OpRegionOp1, OpRegionOp2, ref offset2) == Failure) {
                return Failure;
            }
           
            if (ParseNameString  (out result.nameString,  ref offset2) == Failure ||
                ParseRegionSpace (out result.regionSpace,  ref offset2) == Failure ||
                ParseRegionOffset(out result.regionOffset, ref offset2) == Failure ||
                ParseRegionLen   (out result.regionLen,    ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // OpRegionOp           := ExtOpPrefix 0x80

        const ByteData OpRegionOp1 = ExtOpPrefix;
        const ByteData OpRegionOp2 = 0x80;

        // RegionSpace          := ByteData       // 0x00 SystemMemory
        //                                        // 0x01 SystemIO
        //                                        // 0x02 PCI_Config
        //                                        // 0x03 EmbeddedControl
        //                                        // 0x04 SMBus
        //                                        // 0x05 CMOS
        //                                        // 0x06 PciBarTarget
        //                                        // 0x80-0xFF: User Defined

        public class RegionSpace : AmlParserNode
        {
            public ByteData byteData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseRegionSpace(out RegionSpace result, ref int offset)
        {
            int offset2 = offset;
            result = new RegionSpace();
            result.byteData = stream.ReadByteData(ref offset2);
            offset = offset2;
            return Success;
        }

        // RegionOffset         := TermArg => Integer

        public class RegionOffset : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseRegionOffset(out RegionOffset result, ref int offset)
        {
            int offset2 = offset;
            result = new RegionOffset();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // RegionLen            := TermArg => Integer

        public class RegionLen : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseRegionLen(out RegionLen result, ref int offset)
        {
            int offset2 = offset;
            result = new RegionLen();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // DefPowerRes          := PowerResOp PkgLength NameString SystemLevel ResourceOrder AmlObjectList
        
        public class DefPowerRes : AmlParserNode
        {
            public NameString    nameString;
            public SystemLevel   systemLevel;
            public ResourceOrder resourceOrder;
            public AmlObject[]   amlObjectList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefPowerRes(out DefPowerRes result, ref int offset)
        {
            int offset2 = offset;
            result = new DefPowerRes();
            if (CheckTwoBytePrefix(PowerResOp1, PowerResOp2, ref offset2) == Failure) {
                return Failure;
            }
          
            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }
            
            if (ParseNameString   (out result.nameString,   ref offset2) == Failure) {
                return Failure;
            }

            AbsoluteNodePath oldNodePath = currentNodePath;
            if (acpiNamespace != null) {
                currentNodePath = acpiNamespace.LookupNode(result.nameString.nodePath, currentNodePath).Path;
            }

            if (ParseSystemLevel  (out result.systemLevel,   ref offset2) == Failure ||
                ParseResourceOrder(out result.resourceOrder, ref offset2) == Failure ||
                ParseAmlObjectList(out result.amlObjectList, ref offset2, endOffset) == Failure) {
                return Failure;
            }

            currentNodePath = oldNodePath;

            offset = offset2;
            return Success;
        }
        
        // PowerResOp           := ExtOpPrefix 0x84

        const ByteData PowerResOp1 = ExtOpPrefix;
        const ByteData PowerResOp2 = 0x84;

        // SystemLevel          := ByteData

        public class SystemLevel : AmlParserNode
        {
            public ByteData byteData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseSystemLevel(out SystemLevel result, ref int offset)
        {
            int offset2 = offset;
            result = new SystemLevel();
            result.byteData = stream.ReadByteData(ref offset2);
            offset = offset2;
            return Success;
        }

        // ResourceOrder        := WordData
 
        public class ResourceOrder : AmlParserNode
        {
            public WordData wordData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseResourceOrder(out ResourceOrder result, ref int offset)
        {
            int offset2 = offset;
            result = new ResourceOrder();
            result.wordData = stream.ReadWordData(ref offset2);
            offset = offset2;
            return Success;
        }

        // DefProcessor         := ProcessorOp PkgLength NameString ProcID PblkAddr PblkLen AmlObjectList
        
        public class DefProcessor : AmlParserNode
        {
            public NameString  nameString;
            public ProcID      procID;
            public PblkAddr    pblkAddr;
            public PblkLen     pblkLen;
            public AmlObject[] amlObjectList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefProcessor(out DefProcessor result, ref int offset)
        {
            int offset2 = offset;
            result = new DefProcessor();
            if (CheckTwoBytePrefix(ProcessorOp1, ProcessorOp2, ref offset2) == Failure) {
                return Failure;
            }
          
            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }
            
            if (ParseNameString   (out result.nameString,   ref offset2) == Failure) {
                return Failure;
            }

            AbsoluteNodePath oldNodePath = currentNodePath;
            if (acpiNamespace != null) {
                currentNodePath = acpiNamespace.LookupNode(result.nameString.nodePath, currentNodePath).Path;
            }

            if (ParseProcID       (out result.procID,        ref offset2) == Failure ||
                ParsePblkAddr     (out result.pblkAddr,      ref offset2) == Failure ||
                ParsePblkLen      (out result.pblkLen,       ref offset2) == Failure ||
                ParseAmlObjectList(out result.amlObjectList, ref offset2, endOffset) == Failure) {
                return Failure;
            }

            currentNodePath = oldNodePath;

            offset = offset2;
            return Success;
        }

        // ProcessorOp          := ExtOpPrefix 0x83

        const ByteData ProcessorOp1 = ExtOpPrefix;
        const ByteData ProcessorOp2 = 0x83;

        // ProcID               := ByteData

        public class ProcID : AmlParserNode
        {
            public ByteData byteData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseProcID(out ProcID result, ref int offset)
        {
            int offset2 = offset;
            result = new ProcID();
            result.byteData = stream.ReadByteData(ref offset2);
            offset = offset2;
            return Success;
        }

        // PblkAddr             := DWordData

        public class PblkAddr : AmlParserNode
        {
            public DWordData dWordData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParsePblkAddr(out PblkAddr result, ref int offset)
        {
            int offset2 = offset;
            result = new PblkAddr();
            result.dWordData = stream.ReadDWordData(ref offset2);
            offset = offset2;
            return Success;
        }

        // PblkLen              := ByteData

        public class PblkLen : AmlParserNode
        {
            public ByteData byteData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParsePblkLen(out PblkLen result, ref int offset)
        {
            int offset2 = offset;
            result = new PblkLen();
            result.byteData = stream.ReadByteData(ref offset2);
            offset = offset2;
            return Success;
        }

        // DefThermalZone       := ThermalZoneOp PkgLength NameString AmlObjectList
        
        public class DefThermalZone : AmlParserNode
        {
            public NameString  nameString;
            public AmlObject[] amlObjectList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefThermalZone(out DefThermalZone result, ref int offset)
        {
            int offset2 = offset;
            result = new DefThermalZone();
            if (CheckTwoBytePrefix(ThermalZoneOp1, ThermalZoneOp2, ref offset2) == Failure) {
                return Failure;
            }
          
            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }
            
            if (ParseNameString   (out result.nameString,   ref offset2) == Failure) {
                return Failure;
            }

            AbsoluteNodePath oldNodePath = currentNodePath;
            if (acpiNamespace != null) {
                currentNodePath = acpiNamespace.LookupNode(result.nameString.nodePath, currentNodePath).Path;
            }

            if (ParseAmlObjectList(out result.amlObjectList, ref offset2, endOffset) == Failure) {
                return Failure;
            }

            currentNodePath = oldNodePath;

            offset = offset2;
            return Success;
        }

        // ThermalZoneOp        := ExtOpPrefix 0x85

        const ByteData ThermalZoneOp1 = ExtOpPrefix;
        const ByteData ThermalZoneOp2 = 0x85;

        // 18.2.5.3 Type 1 Opcodes Encoding

        // [Type 1 opcodes involve mainly control flow and some high-level operations.
        //  They are only found inside methods.]
        // Type1Opcode          := DefBreak | DefBreakPoint | DefContinue | DefFatal |
        //                         DefIfElse | DefLoad | DefNoop | DefNotify | 
        //                         DefRelease | DefReset | DefReturn | DefSignal |
        //                         DefSleep | DefStall | DefUnload | DefWhile
        // See AmlParser.csunion

        private ParseSuccess ParseType1Opcode(out Type1Opcode result, ref int offset, int endOffset)
        {
            int offset2 = offset;

            DefBreak      defBreak;
            DefBreakPoint defBreakPoint;
            DefContinue   defContinue;
            DefFatal      defFatal;
            DefIfElse     defIfElse;
            DefLoad       defLoad;
            DefNoop       defNoop;
            DefNotify     defNotify;
            DefRelease    defRelease;
            DefReset      defReset;
            DefReturn     defReturn;
            DefSignal     defSignal;
            DefSleep      defSleep;
            DefStall      defStall;
            DefUnload     defUnload;
            DefWhile      defWhile;
            if (ParseDefBreak     (out defBreak,     ref offset2) == Success) {
                result = Type1Opcode.CreateDefBreak(defBreak);
            }
            else if (ParseDefBreakPoint(out defBreakPoint, ref offset2) == Success) {
                result = Type1Opcode.CreateDefBreakPoint(defBreakPoint);
            }
            else if (ParseDefContinue  (out defContinue,   ref offset2) == Success) {
                result = Type1Opcode.CreateDefContinue(defContinue);
            }
            else if (ParseDefFatal     (out defFatal,      ref offset2) == Success) {
                result = Type1Opcode.CreateDefFatal(defFatal);
            }
            else if (ParseDefIfElse    (out defIfElse,     ref offset2, endOffset) == Success) {
                result = Type1Opcode.CreateDefIfElse(defIfElse);
            }
            else if (ParseDefLoad      (out defLoad,       ref offset2) == Success) {
                result = Type1Opcode.CreateDefLoad(defLoad);
            }
            else if (ParseDefNoop      (out defNoop,       ref offset2) == Success) {
                result = Type1Opcode.CreateDefNoop(defNoop);
            }
            else if (ParseDefNotify    (out defNotify,     ref offset2) == Success) {
                result = Type1Opcode.CreateDefNotify(defNotify);
            }
            else if (ParseDefRelease   (out defRelease,    ref offset2) == Success) {
                result = Type1Opcode.CreateDefRelease(defRelease);
            }
            else if (ParseDefReset     (out defReset,      ref offset2) == Success) {
                result = Type1Opcode.CreateDefReset(defReset);
            }
            else if (ParseDefReturn    (out defReturn,     ref offset2) == Success) {
                result = Type1Opcode.CreateDefReturn(defReturn);
            }
            else if (ParseDefSignal    (out defSignal,     ref offset2) == Success) {
                result = Type1Opcode.CreateDefSignal(defSignal);
            }
            else if (ParseDefSleep     (out defSleep,      ref offset2) == Success) {
                result = Type1Opcode.CreateDefSleep(defSleep);
            }
            else if (ParseDefStall     (out defStall,      ref offset2) == Success) {
                result = Type1Opcode.CreateDefStall(defStall);
            }
            else if (ParseDefUnload    (out defUnload,     ref offset2) == Success) {
                result = Type1Opcode.CreateDefUnload(defUnload);
            }
            else if (ParseDefWhile     (out defWhile,      ref offset2) == Success) {
                result = Type1Opcode.CreateDefWhile(defWhile);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefBreak             := BreakOp

        public class DefBreak : AmlParserNode
        {
            // No data
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefBreak(out DefBreak result, ref int offset)
        {
            int offset2 = offset;
            result = new DefBreak();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != BreakOp) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // BreakOp              := 0xA5

        const ByteData BreakOp = 0xA5;

        // DefBreakPoint        := BreakPointOp

        public class DefBreakPoint : AmlParserNode
        {
            // No data
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefBreakPoint(out DefBreakPoint result, ref int offset)
        {
            int offset2 = offset;
            result = new DefBreakPoint();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != BreakPointOp) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // BreakPointOp         := 0xCC

        const ByteData BreakPointOp = 0xCC;

        // DefContinue          := ContinueOp

        public class DefContinue : AmlParserNode
        {
            // No data
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefContinue(out DefContinue result, ref int offset)
        {
            int offset2 = offset;
            result = new DefContinue();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ContinueOp) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
 
        // ContinueOp           := 0x9F

        const ByteData ContinueOp = 0x9F;

        // DefElse              := Nothing | <ElseOp PkgLength TermList>

        public class DefElse : AmlParserNode
        {
            public TermObj[] termList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefElse(out DefElse result, ref int offset, int endOffset)
        {
            int offset2 = offset;
            result = new DefElse();
            ByteData prefix;

            if (offset >= endOffset) {
                return Success; // Empty else clause
            }
            if (!stream.TryReadByteData(ref offset2, out prefix)) {
                return Success; // Sometimes an if with no else is at the end of the stream
            }
            if (prefix != ElseOp) {
                result.termList = null;
                return Success;
            }

            int endOffsetBody;
            if (ParsePkgLengthEndOffset(out endOffsetBody, ref offset2) == Failure) {
                return Failure;
            }
            
            if (ParseTermList(out result.termList, ref offset2, endOffsetBody) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
         
        // ElseOp               := 0xA1

        const ByteData ElseOp = 0xA1;

        // DefFatal             := FatalOp FatalType FatalCode FatalArg

        public class DefFatal : AmlParserNode
        {
            public FatalType fatalType;
            public FatalCode fatalCode;
            public FatalArg  fatalArg;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefFatal(out DefFatal result, ref int offset)
        {
            int offset2 = offset;
            result = new DefFatal();
            if (CheckTwoBytePrefix(FatalOp1, FatalOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseFatalType(out result.fatalType, ref offset2) == Failure ||
                ParseFatalCode(out result.fatalCode, ref offset2) == Failure ||
                ParseFatalArg (out result.fatalArg,  ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // FatalOp              := ExtOpPrefix 0x32

        const ByteData FatalOp1 = ExtOpPrefix;
        const ByteData FatalOp2 = 0x32;

        // FatalType            := ByteData

        public class FatalType : AmlParserNode
        {
            public ByteData byteData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseFatalType(out FatalType result, ref int offset)
        {
            int offset2 = offset;
            result = new FatalType();
            result.byteData = stream.ReadByteData(ref offset2);
            offset = offset2;
            return Success;
        }

        // FatalCode            := DWordData

        public class FatalCode : AmlParserNode
        {
            public DWordData dWordData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseFatalCode(out FatalCode result, ref int offset)
        {
            int offset2 = offset;
            result = new FatalCode();
            result.dWordData = stream.ReadDWordData(ref offset2);
            offset = offset2;
            return Success;
        }

        // FatalArg             := TermArg => Integer

        public class FatalArg : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseFatalArg(out FatalArg result, ref int offset)
        {
            int offset2 = offset;
            result = new FatalArg();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // DefIfElse            := IfOp PkgLength Predicate TermList DefElse

        public class DefIfElse : AmlParserNode
        {
            public Predicate predicate;
            public TermObj[] termList;
            public DefElse defElse;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefIfElse(out DefIfElse result, ref int offset, int endOffset)
        {
            int offset2 = offset;
            result = new DefIfElse();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != IfOp) {
                return Failure;
            }

            int endOffsetThen;
            if (ParsePkgLengthEndOffset(out endOffsetThen, ref offset2) == Failure) {
                return Failure;
            }
            
            // Investigation of ASL compiler output reveals that the PkgLength in this
            // rule includes the if body but not the else clause, which is fortunate
            // since otherwise ambiguities would arise.
            if (ParsePredicate(out result.predicate, ref offset2) == Failure ||
                ParseTermList(out result.termList, ref offset2, endOffsetThen) == Failure ||
                ParseDefElse(out result.defElse, ref offset2, endOffset) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // IfOp                 := 0xA0

        const ByteData IfOp = 0xA0;

        // Predicate            := TermArg => Integer

        public class Predicate : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParsePredicate(out Predicate result, ref int offset)
        {
            int offset2 = offset;
            result = new Predicate();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefLoad              := LoadOp NameString DDBHandleObject

        public class DefLoad : AmlParserNode
        {
            public NameString nameString;
            public DDBHandleObject ddbHandleObject;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLoad(out DefLoad result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLoad();
            if (CheckTwoBytePrefix(LoadOp1, LoadOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseNameString     (out result.nameString,     ref offset2) == Failure ||
                ParseDDBHandleObject(out result.ddbHandleObject, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // LoadOp               := ExtOpPrefix 0x20

        const ByteData LoadOp1 = ExtOpPrefix;
        const ByteData LoadOp2 = 0x20;

        // DDBHandleObject      := SuperName

        public class DDBHandleObject : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDDBHandleObject(out DDBHandleObject result, ref int offset)
        {
            int offset2 = offset;
            result = new DDBHandleObject();

            if (ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefNoop              := NoopOp

        public class DefNoop : AmlParserNode
        {
            // No data
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefNoop(out DefNoop result, ref int offset)
        {
            int offset2 = offset;
            result = new DefNoop();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != NoopOp) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // NoopOp               := 0xA3

        const ByteData NoopOp = 0xA3;

        // DefNotify            := NotifyOp NotifyObject NotifyValue

        public class DefNotify : AmlParserNode
        {
            public NotifyObject notifyObject;
            public NotifyValue notifyValue;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefNotify(out DefNotify result, ref int offset)
        {
            int offset2 = offset;
            result = new DefNotify();

            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != NotifyOp) {
                return Failure;
            }

            if (ParseNotifyObject(out result.notifyObject, ref offset2) == Failure ||
                ParseNotifyValue (out result.notifyValue,  ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // NotifyOp             := 0x86

        const ByteData NotifyOp = 0x86;

        // NotifyObject         := SuperName => ThermalZone | Processor | Device

        public class NotifyObject : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseNotifyObject(out NotifyObject result, ref int offset)
        {
            int offset2 = offset;
            result = new NotifyObject();

            if (ParseSuperName(out result.superName, ref offset2) == Failure /*||
                (!SuperNameEvaluatesTo(result.superName, SuperNameType.ThermalZone) &&
                 !SuperNameEvaluatesTo(result.superName, SuperNameType.Processor) &&
                 !SuperNameEvaluatesTo(result.superName, SuperNameType.Device)) */) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // NotifyValue          := TermArg => Integer

        public class NotifyValue : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseNotifyValue(out NotifyValue result, ref int offset)
        {
            int offset2 = offset;
            result = new NotifyValue();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // DefRelease           := ReleaseOp MutexObject

        public class DefRelease : AmlParserNode
        {
            public MutexObject mutexObject;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefRelease(out DefRelease result, ref int offset)
        {
            int offset2 = offset;
            result = new DefRelease();

            if (CheckTwoBytePrefix(ReleaseOp1, ReleaseOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseMutexObject(out result.mutexObject, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // ReleaseOp            := ExtOpPrefix 0x27

        const ByteData ReleaseOp1 = ExtOpPrefix;
        const ByteData ReleaseOp2 = 0x27;

        // MutexObject          := SuperName

        public class MutexObject : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseMutexObject(out MutexObject result, ref int offset)
        {
            int offset2 = offset;
            result = new MutexObject();

            if (ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefReset             := ResetOp EventObject

        public class DefReset : AmlParserNode
        {
            public EventObject eventObject;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefReset(out DefReset result, ref int offset)
        {
            int offset2 = offset;
            result = new DefReset();

            if (CheckTwoBytePrefix(ResetOp1, ResetOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseEventObject(out result.eventObject, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // ResetOp              := ExtOpPrefix 0x26

        const ByteData ResetOp1 = ExtOpPrefix;
        const ByteData ResetOp2 = 0x26;

        // EventObject          := SuperName

        public class EventObject : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseEventObject(out EventObject result, ref int offset)
        {
            int offset2 = offset;
            result = new EventObject();

            if (ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // DefReturn            := ReturnOp ArgObject

        public class DefReturn : AmlParserNode
        {
            public ArgObject argObject;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefReturn(out DefReturn result, ref int offset)
        {
            int offset2 = offset;
            result = new DefReturn();

            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ReturnOp) {
                return Failure;
            }

            if (ParseArgObject(out result.argObject, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // ReturnOp             := 0xA4

        const ByteData ReturnOp = 0xA4;

        // ArgObject            := TermArg => DataRefObject

        public class ArgObject : AmlParserNode
        {
            public TermArg dataRefObject;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseArgObject(out ArgObject result, ref int offset)
        {
            int offset2 = offset;
            result = new ArgObject();

            if (ParseTermArg(out result.dataRefObject, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.dataRefObject, TermArgType.DataRefObject)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefSignal            := SignalOp EventObject

        public class DefSignal : AmlParserNode
        {
            public EventObject eventObject;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefSignal(out DefSignal result, ref int offset)
        {
            int offset2 = offset;
            result = new DefSignal();

            if (CheckTwoBytePrefix(SignalOp1, SignalOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseEventObject(out result.eventObject, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // SignalOp             := ExtOpPrefix 0x24

        const ByteData SignalOp1 = ExtOpPrefix;
        const ByteData SignalOp2 = 0x24;

        // DefSleep             := SleepOp MsecTime

        public class DefSleep : AmlParserNode
        {
            public MsecTime msecTime;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefSleep(out DefSleep result, ref int offset)
        {
            int offset2 = offset;
            result = new DefSleep();

            if (CheckTwoBytePrefix(SleepOp1, SleepOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseMsecTime(out result.msecTime, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // SleepOp              := ExtOpPrefix 0x22

        const ByteData SleepOp1 = ExtOpPrefix;
        const ByteData SleepOp2 = 0x22;

        // MsecTime             := TermArg => Integer

        public class MsecTime : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseMsecTime(out MsecTime result, ref int offset)
        {
            int offset2 = offset;
            result = new MsecTime();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefStall             := StallOp UsecTime

        public class DefStall : AmlParserNode
        {
            public UsecTime usecTime;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefStall(out DefStall result, ref int offset)
        {
            int offset2 = offset;
            result = new DefStall();

            if (CheckTwoBytePrefix(StallOp1, StallOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseUsecTime(out result.usecTime, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
        
        // StallOp              := ExtOpPrefix 0x21

        const ByteData StallOp1 = ExtOpPrefix;
        const ByteData StallOp2 = 0x21;

        // UsecTime             := TermArg => ByteData

        public class UsecTime : AmlParserNode
        {
            public TermArg byteData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseUsecTime(out UsecTime result, ref int offset)
        {
            int offset2 = offset;
            result = new UsecTime();

            if (ParseTermArg(out result.byteData, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.byteData, TermArgType.ByteData)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefUnload            := UnloadOp DDBHandleObject

        public class DefUnload : AmlParserNode
        {
            public DDBHandleObject ddbHandleObject;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefUnload(out DefUnload result, ref int offset)
        {
            int offset2 = offset;
            result = new DefUnload();
            if (CheckTwoBytePrefix(UnloadOp1, UnloadOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseDDBHandleObject(out result.ddbHandleObject, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // UnloadOp             := ExtOpPrefix 0x2A

        const ByteData UnloadOp1 = ExtOpPrefix;
        const ByteData UnloadOp2 = 0x2A;

        // DefWhile             := WhileOp PkgLength Predicate TermList

        public class DefWhile : AmlParserNode
        {
            public Predicate predicate;
            public TermObj[] termList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefWhile(out DefWhile result, ref int offset)
        {
            int offset2 = offset;
            result = new DefWhile();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != WhileOp) {
                return Failure;
            }

            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }
            
            if (ParsePredicate(out result.predicate, ref offset2) == Failure ||
                ParseTermList (out result.termList,  ref offset2, endOffset) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // WhileOp              := 0xA2

        const ByteData WhileOp = 0xA2;

        // 18.2.5.4 Type 2 Opcodes Encoding

        // [Type 2 opcodes primarily manipulate primitive values (arithmetic, comparison,
        //  etc.) and can also refer to objects through UserTermObj. They are only found
        //  inside methods.]
        // Type2Opcode          := DefAcquire | DefAdd | DefAnd | DefBuffer |
        //                         DefConcat | DefConcatRes | DefCondRefOf |
        //                         DefCopyObject | DefDecrement | DefDerefOf |
        //                         DefDivide | DefFindSetLeftBit | DefFindSetRightBit |
        //                         DefFromBCD | DefIncrement | DefIndex | DefLAnd |
        //                         DefLEqual | DefLGreater | DefLGreaterEqual |
        //                         DefLLess | DefLLessEqual | DefMid | DefLNot |
        //                         DefLNotEqual | DefLoadTable | DefLOr | DefMatch |
        //                         DefMod | DefMultiply | DefNAnd | DefNOr | DefNot |
        //                         DefObjectType | DefOr | DefPackage | DefVarPackage |
        //                         DefRefOf | DefShiftLeft | DefShiftRight | DefSizeOf |
        //                         DefStore | DefSubtract | DefTimer | DefToBCD |
        //                         DefToBuffer | DefToDecimalString | DefToHexString |
        //                         DefToInteger | DefToString | DefWait | DefXOr |
        //                         UserTermObj
        // See AmlParser.csunion

        private ParseSuccess ParseType2Opcode(out Type2Opcode result, ref int offset)
        {
            int offset2 = offset;

            DefAcquire defAcquire;
            DefAdd defAdd;
            DefAnd defAnd;
            DefBuffer defBuffer;
            DefConcat defConcat;
            DefConcatRes defConcatRes;
            DefCondRefOf defCondRefOf;
            DefCopyObject defCopyObject;
            DefDecrement defDecrement;
            DefDerefOf defDerefOf;
            DefDivide defDivide;
            DefFindSetLeftBit defFindSetLeftBit;
            DefFindSetRightBit defFindSetRightBit;
            DefFromBCD defFromBCD;
            DefIncrement defIncrement;
            DefIndex defIndex;
            DefLAnd defLAnd;
            DefLEqual defLEqual;
            DefLGreater defLGreater;
            DefLGreaterEqual defLGreaterEqual;
            DefLLess defLLess;
            DefLLessEqual defLLessEqual;
            DefMid defMid;
            DefLNot defLNot;
            DefLNotEqual defLNotEqual;
            DefLoadTable defLoadTable;
            DefLOr defLOr;
            DefMatch defMatch;
            DefMod defMod;
            DefMultiply defMultiply;
            DefNAnd defNAnd;
            DefNOr defNOr;
            DefNot defNot;
            DefObjectType defObjectType;
            DefOr defOr;
            DefPackage defPackage;
            DefVarPackage defVarPackage;
            DefRefOf defRefOf;
            DefShiftLeft defShiftLeft;
            DefShiftRight defShiftRight;
            DefSizeOf defSizeOf;
            DefStore defStore;
            DefSubtract defSubtract;
            DefTimer defTimer;
            DefToBCD defToBCD;
            DefToBuffer defToBuffer;
            DefToDecimalString defToDecimalString;
            DefToHexString defToHexString;
            DefToInteger defToInteger;
            DefToString defToString;
            DefWait defWait;
            DefXOr defXOr;
            UserTermObj userTermObj;

            if (ParseDefAcquire             (out defAcquire,         ref offset2) == Success) {
                result = Type2Opcode.CreateDefAcquire(defAcquire);                
            }
            else if (ParseDefAdd            (out defAdd,             ref offset2) == Success) {
                result = Type2Opcode.CreateDefAdd(defAdd);
            }
            else if (ParseDefAnd            (out defAnd,             ref offset2) == Success) {
                result = Type2Opcode.CreateDefAnd(defAnd);
            }
            else if (ParseDefBuffer         (out defBuffer,          ref offset2) == Success) {
                result = Type2Opcode.CreateDefBuffer(defBuffer);
            }
            else if (ParseDefConcat         (out defConcat,          ref offset2) == Success) {
                result = Type2Opcode.CreateDefConcat(defConcat);
            }
            else if (ParseDefConcatRes      (out defConcatRes,       ref offset2) == Success) {
                result = Type2Opcode.CreateDefConcatRes(defConcatRes);
            }
            else if (ParseDefCondRefOf      (out defCondRefOf,       ref offset2) == Success) {
                result = Type2Opcode.CreateDefCondRefOf(defCondRefOf);
            }
            else if (ParseDefCopyObject     (out defCopyObject,      ref offset2) == Success) {
                result = Type2Opcode.CreateDefCopyObject(defCopyObject);
            }
            else if (ParseDefDecrement      (out defDecrement,       ref offset2) == Success) {
                result = Type2Opcode.CreateDefDecrement(defDecrement);
            }
            else if (ParseDefDerefOf        (out defDerefOf,         ref offset2) == Success) {
                result = Type2Opcode.CreateDefDerefOf(defDerefOf);
            }
            else if (ParseDefDivide         (out defDivide,          ref offset2) == Success) {
                result = Type2Opcode.CreateDefDivide(defDivide);
            }
            else if (ParseDefFindSetLeftBit (out defFindSetLeftBit,  ref offset2) == Success) {
                result = Type2Opcode.CreateDefFindSetLeftBit(defFindSetLeftBit);
            }
            else if (ParseDefFindSetRightBit(out defFindSetRightBit, ref offset2) == Success) {
                result = Type2Opcode.CreateDefFindSetRightBit(defFindSetRightBit);
            }
            else if (ParseDefFromBCD        (out defFromBCD,         ref offset2) == Success) {
                result = Type2Opcode.CreateDefFromBCD(defFromBCD);
            }
            else if (ParseDefIncrement      (out defIncrement,       ref offset2) == Success) {
                result = Type2Opcode.CreateDefIncrement(defIncrement);
            }
            else if (ParseDefIndex          (out defIndex,           ref offset2) == Success) {
                result = Type2Opcode.CreateDefIndex(defIndex);
            }
            else if (ParseDefLAnd           (out defLAnd,            ref offset2) == Success) {
                result = Type2Opcode.CreateDefLAnd(defLAnd);
            }
            else if (ParseDefLEqual         (out defLEqual,          ref offset2) == Success) {
                result = Type2Opcode.CreateDefLEqual(defLEqual);
            }
            else if (ParseDefLGreater       (out defLGreater,        ref offset2) == Success) {
                result = Type2Opcode.CreateDefLGreater(defLGreater);
            }
            else if (ParseDefLGreaterEqual  (out defLGreaterEqual,   ref offset2) == Success) {
                result = Type2Opcode.CreateDefLGreaterEqual(defLGreaterEqual);
            }
            else if (ParseDefLLess          (out defLLess,           ref offset2) == Success) {
                result = Type2Opcode.CreateDefLLess(defLLess);
            }
            else if (ParseDefLLessEqual     (out defLLessEqual,      ref offset2) == Success) {
                result = Type2Opcode.CreateDefLLessEqual(defLLessEqual);
            }
            else if (ParseDefMid            (out defMid,             ref offset2) == Success) {
                result = Type2Opcode.CreateDefMid(defMid);
            }
            else if (ParseDefLNot           (out defLNot,            ref offset2) == Success) {
                result = Type2Opcode.CreateDefLNot(defLNot);
            }
            else if (ParseDefLNotEqual      (out defLNotEqual,       ref offset2) == Success) {
                result = Type2Opcode.CreateDefLNotEqual(defLNotEqual);
            }
            else if (ParseDefLoadTable      (out defLoadTable,       ref offset2) == Success) {
                result = Type2Opcode.CreateDefLoadTable(defLoadTable);
            }
            else if (ParseDefLOr            (out defLOr,             ref offset2) == Success) {
                result = Type2Opcode.CreateDefLOr(defLOr);
            }
            else if (ParseDefMatch          (out defMatch,           ref offset2) == Success) {
                result = Type2Opcode.CreateDefMatch(defMatch);
            }
            else if (ParseDefMod            (out defMod,             ref offset2) == Success) {
                result = Type2Opcode.CreateDefMod(defMod);
            }
            else if (ParseDefMultiply       (out defMultiply,        ref offset2) == Success) {
                result = Type2Opcode.CreateDefMultiply(defMultiply);
            }
            else if (ParseDefNAnd           (out defNAnd,            ref offset2) == Success) {
                result = Type2Opcode.CreateDefNAnd(defNAnd);
            }
            else if (ParseDefNOr            (out defNOr,             ref offset2) == Success) {
                result = Type2Opcode.CreateDefNOr(defNOr);
            }
            else if (ParseDefNot            (out defNot,             ref offset2) == Success) {
                result = Type2Opcode.CreateDefNot(defNot);
            }
            else if (ParseDefObjectType     (out defObjectType,      ref offset2) == Success) {
                result = Type2Opcode.CreateDefObjectType(defObjectType);
            }
            else if (ParseDefOr             (out defOr,              ref offset2) == Success) {
                result = Type2Opcode.CreateDefOr(defOr);
            }
            else if (ParseDefPackage        (out defPackage,         ref offset2) == Success) {
                result = Type2Opcode.CreateDefPackage(defPackage);
            }
            else if (ParseDefVarPackage     (out defVarPackage,      ref offset2) == Success) {
                result = Type2Opcode.CreateDefVarPackage(defVarPackage);
            }
            else if (ParseDefRefOf          (out defRefOf,           ref offset2) == Success) {
                result = Type2Opcode.CreateDefRefOf(defRefOf);
            }
            else if (ParseDefShiftLeft      (out defShiftLeft,       ref offset2) == Success) {
                result = Type2Opcode.CreateDefShiftLeft(defShiftLeft);
            }
            else if (ParseDefShiftRight     (out defShiftRight,      ref offset2) == Success) {
                result = Type2Opcode.CreateDefShiftRight(defShiftRight);
            }
            else if (ParseDefSizeOf         (out defSizeOf,          ref offset2) == Success) {
                result = Type2Opcode.CreateDefSizeOf(defSizeOf);
            }
            else if (ParseDefStore          (out defStore,           ref offset2) == Success) {
                result = Type2Opcode.CreateDefStore(defStore);
            }
            else if (ParseDefSubtract       (out defSubtract,        ref offset2) == Success) {
                result = Type2Opcode.CreateDefSubtract(defSubtract);
            }
            else if (ParseDefTimer          (out defTimer,           ref offset2) == Success) {
                result = Type2Opcode.CreateDefTimer(defTimer);
            }
            else if (ParseDefToBCD          (out defToBCD,           ref offset2) == Success) {
                result = Type2Opcode.CreateDefToBCD(defToBCD);
            }
            else if (ParseDefToBuffer       (out defToBuffer,        ref offset2) == Success) {
                result = Type2Opcode.CreateDefToBuffer(defToBuffer);
            }
            else if (ParseDefToDecimalString(out defToDecimalString, ref offset2) == Success) {
                result = Type2Opcode.CreateDefToDecimalString(defToDecimalString);
            }
            else if (ParseDefToHexString    (out defToHexString,     ref offset2) == Success) {
                result = Type2Opcode.CreateDefToHexString(defToHexString);
            }
            else if (ParseDefToInteger      (out defToInteger,       ref offset2) == Success) {
                result = Type2Opcode.CreateDefToInteger(defToInteger);
            }
            else if (ParseDefToString       (out defToString,        ref offset2) == Success) {
                result = Type2Opcode.CreateDefToString(defToString);
            }
            else if (ParseDefWait           (out defWait,            ref offset2) == Success) {
                result = Type2Opcode.CreateDefWait(defWait);
            }
            else if (ParseDefXOr            (out defXOr,             ref offset2) == Success) {
                result = Type2Opcode.CreateDefXOr(defXOr);
            }
            else if (ParseUserTermObj       (out userTermObj,        ref offset2) == Success) {
                result = Type2Opcode.CreateUserTermObj(userTermObj);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // Type6Opcode          := DefRefOf | DefDerefOf | DefIndex | UserTermObj


        private ParseSuccess ParseType6Opcode(out Type6Opcode result, ref int offset)
        {
            int offset2 = offset;

            DefRefOf defRefOf;
            DefDerefOf defDerefOf;
            DefIndex defIndex;
            UserTermObj userTermObj;

            if (ParseDefRefOf   (out defRefOf,    ref offset2) == Success) {
                result = Type6Opcode.CreateDefRefOf(defRefOf);
            }
            else if (ParseDefDerefOf (out defDerefOf,  ref offset2) == Success) {
                result = Type6Opcode.CreateDefDerefOf(defDerefOf);
            }
            else if (ParseDefIndex   (out defIndex,    ref offset2) == Success) {
                result = Type6Opcode.CreateDefIndex(defIndex);
            }
            else if (ParseUserTermObj(out userTermObj, ref offset2) == Success) {
                result = Type6Opcode.CreateUserTermObj(userTermObj);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefAcquire           := AcquireOp MutexObject TimeOut

        public class DefAcquire : AmlParserNode
        {
            public MutexObject mutexObject;
            public TimeOut timeOut;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefAcquire(out DefAcquire result, ref int offset)
        {
            int offset2 = offset;
            result = new DefAcquire();
            if (CheckTwoBytePrefix(AcquireOp1, AcquireOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseMutexObject(out result.mutexObject, ref offset2) == Failure ||
                ParseTimeOut    (out result.timeOut,     ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // AcquireOp            := ExtOpPrefix 0x23

        const ByteData AcquireOp1 = ExtOpPrefix;
        const ByteData AcquireOp2 = 0x23;

        // TimeOut              := WordData

        public class TimeOut : AmlParserNode
        {
            public WordData wordData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseTimeOut(out TimeOut result, ref int offset)
        {
            int offset2 = offset;
            result = new TimeOut();
            result.wordData = stream.ReadWordData(ref offset2);
            offset = offset2;
            return Success;
        }

        // DefAdd               := AddOp Operand Operand Target

        public class DefAdd : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefAdd(out DefAdd result, ref int offset)
        {
            int offset2 = offset;
            result = new DefAdd();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != AddOp) {
                return Failure;
            }
            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure ||
                ParseTarget (out result.target,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // AddOp                := 0x72

        const ByteData AddOp = 0x72;

        // Operand              := TermArg => Integer

        public class Operand : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseOperand(out Operand result, ref int offset)
        {
            int offset2 = offset;
            result = new Operand();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefAnd               := AndOp Operand Operand Target

        public class DefAnd : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefAnd(out DefAnd result, ref int offset)
        {
            int offset2 = offset;
            result = new DefAnd();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != AndOp) {
                return Failure;
            }
            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure ||
                ParseTarget (out result.target,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // AndOp                := 0x7B

        const ByteData AndOp = 0x7B;

        // DefBuffer            := BufferOp PkgLength BufferSize ByteList

        public class DefBuffer : AmlParserNode
        {
            public BufferSize bufferSize;
            public ByteData[] byteList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefBuffer(out DefBuffer result, ref int offset)
        {
            int offset2 = offset;
            result = new DefBuffer();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != BufferOp) {
                return Failure;
            }

            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }
            
            if (ParseBufferSize(out result.bufferSize, ref offset2) == Failure ||
                ParseByteList  (out result.byteList,   ref offset2, endOffset) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // BufferOp             := 0x11

        const ByteData BufferOp = 0x11;

        // BufferSize           := TermArg => Integer

        public class BufferSize : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseBufferSize(out BufferSize result, ref int offset)
        {
            int offset2 = offset;
            result = new BufferSize();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefConcat            := ConcatOp Data Data Target

        public class DefConcat : AmlParserNode
        {
            public Data leftData;
            public Data rightData;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefConcat(out DefConcat result, ref int offset)
        {
            int offset2 = offset;
            result = new DefConcat();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ConcatOp) {
                return Failure;
            }
            if (ParseData(out result.leftData, ref offset2) == Failure ||
                ParseData(out result.rightData, ref offset2) == Failure ||
                ParseTarget (out result.target, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // ConcatOp             := 0x73

        const ByteData ConcatOp = 0x73;

        // Data                 := TermArg => ComputationalData

        public class Data : AmlParserNode
        {
            public TermArg computationalData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseData(out Data result, ref int offset)
        {
            int offset2 = offset;
            result = new Data();

            if (ParseTermArg(out result.computationalData, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.computationalData, TermArgType.ComputationalData)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefConcatRes         := ConcatResOp BufData BufData Target

        public class DefConcatRes : AmlParserNode
        {
            public BufData leftBufData;
            public BufData rightBufData;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefConcatRes(out DefConcatRes result, ref int offset)
        {
            int offset2 = offset;
            result = new DefConcatRes();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ConcatResOp) {
                return Failure;
            }
            if (ParseBufData(out result.leftBufData, ref offset2) == Failure ||
                ParseBufData(out result.rightBufData, ref offset2) == Failure ||
                ParseTarget (out result.target,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // ConcatResOp          := 0x84

        const ByteData ConcatResOp = 0x84;

        // BufData              := TermArg => Buffer

        public class BufData : AmlParserNode
        {
            public TermArg buffer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseBufData(out BufData result, ref int offset)
        {
            int offset2 = offset;
            result = new BufData();

            if (ParseTermArg(out result.buffer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.buffer, TermArgType.Buffer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefCondRefOf         := CondRefOfOp SuperName Target

        public class DefCondRefOf : AmlParserNode
        {
            public SuperName superName;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefCondRefOf(out DefCondRefOf result, ref int offset)
        {
            int offset2 = offset;
            result = new DefCondRefOf();
            if (CheckTwoBytePrefix(CondRefOfOp1, CondRefOfOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseSuperName(out result.superName, ref offset2) == Failure ||
                ParseTarget   (out result.target,     ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // CondRefOfOp          := ExtOpPrefix 0x12

        const ByteData CondRefOfOp1 = ExtOpPrefix;
        const ByteData CondRefOfOp2 = 0x12;

        // DefCopyObject        := CopyObjectOp TermArg SimpleName

        public class DefCopyObject : AmlParserNode
        {
            public TermArg termArg;
            public SimpleName simpleName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefCopyObject(out DefCopyObject result, ref int offset)
        {
            int offset2 = offset;
            result = new DefCopyObject();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != CopyObjectOp) {
                return Failure;
            }
            if (ParseTermArg   (out result.termArg,   ref offset2) == Failure ||
                ParseSimpleName(out result.simpleName, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // CopyObjectOp         := 0x9D

        const ByteData CopyObjectOp = 0x9D;

        // DefDecrement         := DecrementOp SuperName

        public class DefDecrement : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefDecrement(out DefDecrement result, ref int offset)
        {
            int offset2 = offset;
            result = new DefDecrement();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != DecrementOp) {
                return Failure;
            }
            if (ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // DecrementOp          := 0x76

        const ByteData DecrementOp = 0x76;

        // DefDerefOf           := DerefOfOp ObjReference

        public class DefDerefOf : AmlParserNode
        {
            public ObjReference objReference;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefDerefOf(out DefDerefOf result, ref int offset)
        {
            int offset2 = offset;
            result = new DefDerefOf();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != DerefOfOp) {
                return Failure;
            }
            if (ParseObjReference(out result.objReference, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // DerefOfOp            := 0x83

        const ByteData DerefOfOp = 0x83;

        // ObjReference         := TermArg => ObjectReference | StringConst

        public class ObjReference : AmlParserNode
        {
            public TermArg termArg;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseObjReference(out ObjReference result, ref int offset)
        {
            int offset2 = offset;
            result = new ObjReference();

            if (ParseTermArg(out result.termArg, ref offset2) == Failure /*||
                (!TermArgEvaluatesTo(result.termArg, TermArgType.ObjectReference) &&
                 !TermArgEvaluatesTo(result.termArg, TermArgType.StringConst))*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefDivide            := DivideOp Dividend Divisor Remainder Quotient

        public class DefDivide : AmlParserNode
        {
            public Dividend dividend;
            public Divisor divisor;
            public Remainder remainder;
            public Quotient quotient;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefDivide(out DefDivide result, ref int offset)
        {
            int offset2 = offset;
            result = new DefDivide();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != DivideOp) {
                return Failure;
            }
            if (ParseDividend (out result.dividend, ref offset2) == Failure ||
                ParseDivisor  (out result.divisor,   ref offset2) == Failure ||
                ParseRemainder(out result.remainder, ref offset2) == Failure ||
                ParseQuotient (out result.quotient,  ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // DivideOp             := 0x78

        const ByteData DivideOp = 0x78;

        // Dividend             := TermArg => Integer

        public class Dividend : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDividend(out Dividend result, ref int offset)
        {
            int offset2 = offset;
            result = new Dividend();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // Divisor              := TermArg => Integer

        public class Divisor : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDivisor(out Divisor result, ref int offset)
        {
            int offset2 = offset;
            result = new Divisor();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // Remainder            := Target

        public class Remainder : AmlParserNode
        {
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseRemainder(out Remainder result, ref int offset)
        {
            int offset2 = offset;
            result = new Remainder();

            if (ParseTarget(out result.target, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // Quotient             := Target

        public class Quotient : AmlParserNode
        {
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseQuotient(out Quotient result, ref int offset)
        {
            int offset2 = offset;
            result = new Quotient();

            if (ParseTarget(out result.target, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefFindSetLeftBit    := FindSetLeftBitOp Operand Target

        public class DefFindSetLeftBit : AmlParserNode
        {
            public Operand operand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefFindSetLeftBit(out DefFindSetLeftBit result, ref int offset)
        {
            int offset2 = offset;
            result = new DefFindSetLeftBit();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != FindSetLeftBitOp) {
                return Failure;
            }
            if (ParseOperand(out result.operand, ref offset2) == Failure ||
                ParseTarget (out result.target,   ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // FindSetLeftBitOp     := 0x81

        const ByteData FindSetLeftBitOp = 0x81;

        // DefFindSetRightBit   := FindSetRightBitOp Operand Target

        public class DefFindSetRightBit : AmlParserNode
        {
            public Operand operand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefFindSetRightBit(out DefFindSetRightBit result, ref int offset)
        {
            int offset2 = offset;
            result = new DefFindSetRightBit();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != FindSetRightBitOp) {
                return Failure;
            }
            if (ParseOperand(out result.operand, ref offset2) == Failure ||
                ParseTarget (out result.target,   ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // FindSetRightBitOp    := 0x82

        const ByteData FindSetRightBitOp = 0x82;

        // DefFromBCD           := FromBCDOp BCDValue Target

        public class DefFromBCD : AmlParserNode
        {
            public BCDValue bcdValue;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefFromBCD(out DefFromBCD result, ref int offset)
        {
            int offset2 = offset;
            result = new DefFromBCD();
            if (CheckTwoBytePrefix(FromBCDOp1, FromBCDOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseBCDValue(out result.bcdValue, ref offset2) == Failure ||
                ParseTarget  (out result.target,    ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // FromBCDOp            := ExtOpPrefix 0x28

        const ByteData FromBCDOp1 = ExtOpPrefix;
        const ByteData FromBCDOp2 = 0x28;

        // BCDValue             := TermArg => Integer

        public class BCDValue : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseBCDValue(out BCDValue result, ref int offset)
        {
            int offset2 = offset;
            result = new BCDValue();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefIncrement         := IncrementOp SuperName

        public class DefIncrement : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefIncrement(out DefIncrement result, ref int offset)
        {
            int offset2 = offset;
            result = new DefIncrement();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != IncrementOp) {
                return Failure;
            }
            if (ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // IncrementOp          := 0x75

        const ByteData IncrementOp = 0x75;

        // DefIndex             := IndexOp BuffPkgStrObj IndexValue Target

        public class DefIndex : AmlParserNode
        {
            public BuffPkgStrObj buffPkgStrObj;
            public IndexValue indexValue;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefIndex(out DefIndex result, ref int offset)
        {
            int offset2 = offset;
            result = new DefIndex();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != IndexOp) {
                return Failure;
            }
            if (ParseBuffPkgStrObj(out result.buffPkgStrObj, ref offset2) == Failure ||
                ParseIndexValue   (out result.indexValue,    ref offset2) == Failure ||
                ParseTarget       (out result.target,        ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // IndexOp              := 0x88

        const ByteData IndexOp = 0x88;

        // BuffPkgStrObj        := TermArg => Buffer | Package | StringConst

        public class BuffPkgStrObj : AmlParserNode
        {
            public TermArg termArg;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseBuffPkgStrObj(out BuffPkgStrObj result, ref int offset)
        {
            int offset2 = offset;
            result = new BuffPkgStrObj();

            if (ParseTermArg(out result.termArg, ref offset2) == Failure /* ||
                (!TermArgEvaluatesTo(result.termArg, TermArgType.Buffer) &&
                 !TermArgEvaluatesTo(result.termArg, TermArgType.Package) &&
                 !TermArgEvaluatesTo(result.termArg, TermArgType.StringConst)) */) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // IndexValue           := TermArg => Integer

        public class IndexValue : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseIndexValue(out IndexValue result, ref int offset)
        {
            int offset2 = offset;
            result = new IndexValue();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefLAnd              := LandOp Operand Operand

        public class DefLAnd : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLAnd(out DefLAnd result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLAnd();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != LandOp) {
                return Failure;
            }
            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // LandOp               := 0x90

        const ByteData LandOp = 0x90;

        // DefLEqual            := LequalOp Operand Operand

        public class DefLEqual : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLEqual(out DefLEqual result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLEqual();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != LequalOp) {
                return Failure;
            }
            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // LequalOp             := 0x93

        const ByteData LequalOp = 0x93;

        // DefLGreater          := LgreaterOp Operand Operand

        public class DefLGreater : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLGreater(out DefLGreater result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLGreater();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != LgreaterOp) {
                return Failure;
            }
            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // LgreaterOp           := 0x94

        const ByteData LgreaterOp = 0x94;

        // DefLGreaterEqual     := LgreaterEqualOp Operand Operand

        public class DefLGreaterEqual : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLGreaterEqual(out DefLGreaterEqual result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLGreaterEqual();
            if (CheckTwoBytePrefix(LgreaterEqualOp1, LgreaterEqualOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // LgreaterEqualOp      := LnotOp LlessOp

        const ByteData LgreaterEqualOp1 = LnotOp;
        const ByteData LgreaterEqualOp2 = LlessOp;

        // DefLLess             := LlessOp Operand Operand

        public class DefLLess : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLLess(out DefLLess result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLLess();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != LlessOp) {
                return Failure;
            }
            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // LlessOp              := 0x95

        const ByteData LlessOp = 0x95;

        // DefLLessEqual        := LlessEqualOp Operand Operand

        public class DefLLessEqual : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLLessEqual(out DefLLessEqual result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLLessEqual();
            if (CheckTwoBytePrefix(LlessEqualOp1, LlessEqualOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // LlessEqualOp         := LnotOp LgreaterOp

        const ByteData LlessEqualOp1 = LnotOp;
        const ByteData LlessEqualOp2 = LgreaterOp;

        // DefLNot              := LnotOp Operand

        public class DefLNot : AmlParserNode
        {
            public Operand operand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLNot(out DefLNot result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLNot();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != LnotOp) {
                return Failure;
            }
            if (ParseOperand(out result.operand, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // LnotOp               := 0x92

        const ByteData LnotOp = 0x92;

        // DefLNotEqual         := LnotEqualOp Operand Operand

        public class DefLNotEqual : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLNotEqual(out DefLNotEqual result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLNotEqual();
            if (CheckTwoBytePrefix(LnotEqualOp1, LnotEqualOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // LnotEqualOp          := LnotOp LequalOp

        const ByteData LnotEqualOp1 = LnotOp;
        const ByteData LnotEqualOp2 = LequalOp;

        // DefLoadTable         := LoadTableOp TermArg TermArg TermArg TermArg TermArg TermArg

        public class DefLoadTable : AmlParserNode
        {
            public TermArg signatureString;
            public TermArg oemIDString;
            public TermArg oemTableIDString;
            public TermArg rootPathString;
            public TermArg parameterPathString;
            public TermArg parameterData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLoadTable(out DefLoadTable result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLoadTable();
            if (CheckTwoBytePrefix(LoadTableOp1, LoadTableOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseTermArg(out result.signatureString,    ref offset2) == Failure ||
                ParseTermArg(out result.oemIDString,         ref offset2) == Failure ||
                ParseTermArg(out result.oemTableIDString,    ref offset2) == Failure ||
                ParseTermArg(out result.rootPathString,      ref offset2) == Failure ||
                ParseTermArg(out result.parameterPathString, ref offset2) == Failure ||
                ParseTermArg(out result.parameterData,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // LoadTableOp          := ExtOpPrefix 0x1F

        const ByteData LoadTableOp1 = ExtOpPrefix;
        const ByteData LoadTableOp2 = 0x1F;

        // DefLOr               := LorOp Operand Operand

        public class DefLOr : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefLOr(out DefLOr result, ref int offset)
        {
            int offset2 = offset;
            result = new DefLOr();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != LorOp) {
                return Failure;
            }
            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // LorOp                := 0x91

        const ByteData LorOp = 0x91;

        // DefMatch             := MatchOp SearchPkg MatchOpcode Operand MatchOpcode Operand StartIndex

        public class DefMatch : AmlParserNode
        {
            public SearchPkg searchPkg;
            public MatchOpcode matchOpcode1;
            public Operand operand1;
            public MatchOpcode matchOpcode2;
            public Operand operand2;
            public StartIndex startIndex;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefMatch(out DefMatch result, ref int offset)
        {
            int offset2 = offset;
            result = new DefMatch();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != MatchOp) {
                return Failure;
            }
            if (ParseSearchPkg  (out result.searchPkg,   ref offset2) == Failure ||
                ParseMatchOpcode(out result.matchOpcode1, ref offset2) == Failure ||
                ParseOperand    (out result.operand1,     ref offset2) == Failure ||
                ParseMatchOpcode(out result.matchOpcode2, ref offset2) == Failure ||
                ParseOperand    (out result.operand2,     ref offset2) == Failure ||
                ParseStartIndex (out result.startIndex,   ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // MatchOp              := 0x89

        const ByteData MatchOp = 0x89;

        // SearchPkg            := TermArg => Package

        public class SearchPkg : AmlParserNode
        {
            public TermArg package;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseSearchPkg(out SearchPkg result, ref int offset)
        {
            int offset2 = offset;
            result = new SearchPkg();

            if (ParseTermArg(out result.package, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.package, TermArgType.Package)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // MatchOpcode          := ByteData             // 0 MTR
        //                                              // 1 MEQ
        //                                              // 2 MLE
        //                                              // 3 MLT
        //                                              // 4 MGE
        //                                              // 5 MGT

        public enum MatchOpcode
        {
            MTR = 0,
            MEQ = 1,
            MLE = 2,
            MLT = 3,
            MGE = 4,
            MGT = 5,
            NumMatchOpcodes = 6
        }

        private ParseSuccess ParseMatchOpcode(out MatchOpcode result, ref int offset)
        {
            int offset2 = offset;
            result = new MatchOpcode();

            ByteData b = stream.ReadByteData(ref offset2);
            if (b >= (byte)MatchOpcode.NumMatchOpcodes) {
                return Failure;
            }
            result = (MatchOpcode)b;

            offset = offset2;
            return Success;
        }
        
        // StartIndex           := TermArg => Integer

        public class StartIndex : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseStartIndex(out StartIndex result, ref int offset)
        {
            int offset2 = offset;
            result = new StartIndex();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefMid               := MidOp MidObj TermArg TermArg Target

        public class DefMid : AmlParserNode
        {
            public MidObj midObj;
            public TermArg index;
            public TermArg length;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefMid(out DefMid result, ref int offset)
        {
            int offset2 = offset;
            result = new DefMid();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != MidOp) {
                return Failure;
            }
            if (ParseMidObj (out result.midObj, ref offset2) == Failure ||
                ParseTermArg(out result.index,   ref offset2) == Failure ||
                ParseTermArg(out result.length,  ref offset2) == Failure ||
                ParseTarget (out result.target,  ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // MidOp                := 0x9E

        const ByteData MidOp = 0x9E;

        // MidObj               := TermArg => Buffer | StringConst

        public class MidObj : AmlParserNode
        {
            public TermArg termArg;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseMidObj(out MidObj result, ref int offset)
        {
            int offset2 = offset;
            result = new MidObj();

            if (ParseTermArg(out result.termArg, ref offset2) == Failure /*||
                (!TermArgEvaluatesTo(result.termArg, TermArgType.Buffer) &&
                 !TermArgEvaluatesTo(result.termArg, TermArgType.StringConst))*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefMod               := ModOp Dividend Divisor Target

        public class DefMod : AmlParserNode
        {
            public Dividend dividend;
            public Divisor divisor;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefMod(out DefMod result, ref int offset)
        {
            int offset2 = offset;
            result = new DefMod();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ModOp) {
                return Failure;
            }
            if (ParseDividend (out result.dividend, ref offset2) == Failure ||
                ParseDivisor  (out result.divisor,   ref offset2) == Failure ||
                ParseTarget   (out result.target,    ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // ModOp                := 0x85

        const ByteData ModOp = 0x85;

        // DefMultiply          := MultiplyOp Operand Operand Target

        public class DefMultiply : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefMultiply(out DefMultiply result, ref int offset)
        {
            int offset2 = offset;
            result = new DefMultiply();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != MultiplyOp) {
                return Failure;
            }
            if (ParseOperand (out result.leftOperand, ref offset2) == Failure ||
                ParseOperand (out result.rightOperand, ref offset2) == Failure ||
                ParseTarget  (out result.target,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // MultiplyOp           := 0x77

        const ByteData MultiplyOp = 0x77;

        // DefNAnd              := NandOp Operand Operand Target

        public class DefNAnd : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefNAnd(out DefNAnd result, ref int offset)
        {
            int offset2 = offset;
            result = new DefNAnd();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != NandOp) {
                return Failure;
            }
            if (ParseOperand (out result.leftOperand, ref offset2) == Failure ||
                ParseOperand (out result.rightOperand, ref offset2) == Failure ||
                ParseTarget  (out result.target,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // NandOp               := 0x7C

        const ByteData NandOp = 0x7C;

        // DefNOr               := NorOp Operand Operand Target

        public class DefNOr : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefNOr(out DefNOr result, ref int offset)
        {
            int offset2 = offset;
            result = new DefNOr();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != NorOp) {
                return Failure;
            }
            if (ParseOperand (out result.leftOperand, ref offset2) == Failure ||
                ParseOperand (out result.rightOperand, ref offset2) == Failure ||
                ParseTarget  (out result.target,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
 
        // NorOp                := 0x7E

        const ByteData NorOp = 0x7E;

        // DefNot               := NotOp Operand Target

        public class DefNot : AmlParserNode
        {
            public Operand operand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefNot(out DefNot result, ref int offset)
        {
            int offset2 = offset;
            result = new DefNot();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != NotOp) {
                return Failure;
            }
            if (ParseOperand (out result.operand, ref offset2) == Failure ||
                ParseTarget  (out result.target,   ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // NotOp                := 0x80

        const ByteData NotOp = 0x80;

        // DefObjectType        := ObjectTypeOp SuperName

        public class DefObjectType : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefObjectType(out DefObjectType result, ref int offset)
        {
            int offset2 = offset;
            result = new DefObjectType();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ObjectTypeOp) {
                return Failure;
            }
            if (ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // ObjectTypeOp         := 0x8E

        const ByteData ObjectTypeOp = 0x8E;

        // DefOr                := OrOp Operand Operand Target

        public class DefOr : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefOr(out DefOr result, ref int offset)
        {
            int offset2 = offset;
            result = new DefOr();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != OrOp) {
                return Failure;
            }
            if (ParseOperand (out result.leftOperand, ref offset2) == Failure ||
                ParseOperand (out result.rightOperand, ref offset2) == Failure ||
                ParseTarget  (out result.target,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // OrOp                 := 0x7D

        const ByteData OrOp = 0x7D;

        // DefPackage           := PackageOp PkgLength NumElements PackageElementList

        public class DefPackage : AmlParserNode
        {
            public NumElements numElements;
            public PackageElement[] packageElementList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefPackage(out DefPackage result, ref int offset)
        {
            int offset2 = offset;
            result = new DefPackage();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != PackageOp) {
                return Failure;
            }

            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseNumElements       (out result.numElements,       ref offset2) == Failure ||
                ParsePackageElementList(out result.packageElementList, ref offset2, endOffset) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // PackageOp            := 0x12

        const ByteData PackageOp = 0x12;

        // DefVarPackage        := VarPackageOp PkgLength VarNumElements PackageElementList

        public class DefVarPackage : AmlParserNode
        {
            public VarNumElements varNumElements;
            public PackageElement[] packageElementList;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefVarPackage(out DefVarPackage result, ref int offset)
        {
            int offset2 = offset;
            result = new DefVarPackage();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != VarPackageOp) {
                return Failure;
            }

            int endOffset;
            if (ParsePkgLengthEndOffset(out endOffset, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseVarNumElements    (out result.varNumElements,    ref offset2) == Failure ||
                ParsePackageElementList(out result.packageElementList, ref offset2, endOffset) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // VarPackageOp         := 0x13

        const ByteData VarPackageOp = 0x13;

        // NumElements          := ByteData

        public class NumElements : AmlParserNode
        {
            public ByteData byteData;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseNumElements(out NumElements result, ref int offset)
        {
            int offset2 = offset;
            result = new NumElements();
            result.byteData = stream.ReadByteData(ref offset2);
            offset = offset2;
            return Success;
        }

        // VarNumElements       := TermArg => Integer

        public class VarNumElements : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseVarNumElements(out VarNumElements result, ref int offset)
        {
            int offset2 = offset;
            result = new VarNumElements();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // PackageElementList   := Nothing | <PackageElement PackageElementList>
        // [To make this rule make sense, it needs a length
        //  limit for termination. The rule using it should know this.]

        private class PackageElementList
        {
            ArrayList list = new ArrayList();

            public void Add(PackageElement packageElement)
            {
                list.Add(packageElement);
            }

            public PackageElement[] ToArray()
            {
                return (PackageElement[])list.ToArray(typeof(PackageElement));
            }
        }
        
        private ParseSuccess ParsePackageElementList(out PackageElement[] result, ref int offset, int endOffset)
        {
            result = null;
            PackageElementList packageElements = new PackageElementList();
            int offset2 = offset;

            while (offset2 < endOffset) {
                PackageElement packageElement;
                if (ParsePackageElement(out packageElement, ref offset2) == Failure) {
                    return Failure;
                }
                packageElements.Add(packageElement);
            }
            Debug.Assert(offset2 == endOffset);
            
            result = packageElements.ToArray();
            offset = offset2;
            return Success;
        }

        // PackageElement       := DataRefObject | NameString
        // See AmlParser.csunion

        private ParseSuccess ParsePackageElement(out PackageElement result, ref int offset)
        {
            int offset2 = offset;

            DataRefObject dataRefObject;
            NameString nameString;

            if (ParseDataRefObject(out dataRefObject, ref offset2) == Success) {
                result = PackageElement.CreateDataRefObject(dataRefObject);
            }
            else if (ParseNameString(out nameString, ref offset2) == Success) {
                result = PackageElement.CreateNameString(nameString);
            }
            else {
                result = null;
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefRefOf             := RefOfOp SuperName

        public class DefRefOf : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefRefOf(out DefRefOf result, ref int offset)
        {
            int offset2 = offset;
            result = new DefRefOf();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != RefOfOp) {
                return Failure;
            }
            if (ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // RefOfOp              := 0x71

        const ByteData RefOfOp = 0x71;

        // DefShiftLeft         := ShiftLeftOp Operand ShiftCount Target

        public class DefShiftLeft : AmlParserNode
        {
            public Operand operand;
            public ShiftCount shiftCount;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefShiftLeft(out DefShiftLeft result, ref int offset)
        {
            int offset2 = offset;
            result = new DefShiftLeft();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ShiftLeftOp) {
                return Failure;
            }
            if (ParseOperand   (out result.operand,   ref offset2) == Failure ||
                ParseShiftCount(out result.shiftCount, ref offset2) == Failure ||
                ParseTarget    (out result.target,     ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // ShiftLeftOp          := 0x79

        const ByteData ShiftLeftOp = 0x79;

        // ShiftCount           := TermArg => Integer

        public class ShiftCount : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseShiftCount(out ShiftCount result, ref int offset)
        {
            int offset2 = offset;
            result = new ShiftCount();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DefShiftRight        := ShiftRightOp Operand ShiftCount Target

        public class DefShiftRight : AmlParserNode
        {
            public Operand operand;
            public ShiftCount shiftCount;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefShiftRight(out DefShiftRight result, ref int offset)
        {
            int offset2 = offset;
            result = new DefShiftRight();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ShiftRightOp) {
                return Failure;
            }
            if (ParseOperand   (out result.operand,   ref offset2) == Failure ||
                ParseShiftCount(out result.shiftCount, ref offset2) == Failure ||
                ParseTarget    (out result.target,     ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // ShiftRightOp         := 0x7A

        const ByteData ShiftRightOp = 0x7A;

        // DefSizeOf            := SizeOfOp SuperName

        public class DefSizeOf : AmlParserNode
        {
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefSizeOf(out DefSizeOf result, ref int offset)
        {
            int offset2 = offset;
            result = new DefSizeOf();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != SizeOfOp) {
                return Failure;
            }
            if (ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // SizeOfOp             := 0x87

        const ByteData SizeOfOp = 0x87;

        // DefStore             := StoreOp TermArg SuperName

        public class DefStore : AmlParserNode
        {
            public TermArg termArg;
            public SuperName superName;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefStore(out DefStore result, ref int offset)
        {
            int offset2 = offset;
            result = new DefStore();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != StoreOp) {
                return Failure;
            }
            if (ParseTermArg  (out result.termArg,  ref offset2) == Failure ||
                ParseSuperName(out result.superName, ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
 
        // StoreOp              := 0x70

        const ByteData StoreOp = 0x70;

        // DefSubtract          := SubtractOp Operand Operand Target

        public class DefSubtract : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefSubtract(out DefSubtract result, ref int offset)
        {
            int offset2 = offset;
            result = new DefSubtract();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != SubtractOp) {
                return Failure;
            }
            if (ParseOperand (out result.leftOperand, ref offset2) == Failure ||
                ParseOperand (out result.rightOperand, ref offset2) == Failure ||
                ParseTarget  (out result.target,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // SubtractOp           := 0x74

        const ByteData SubtractOp = 0x74;

        // DefTimer             := TimerOp

        public class DefTimer : AmlParserNode
        {
            // No data
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefTimer(out DefTimer result, ref int offset)
        {
            int offset2 = offset;
            result = new DefTimer();
            if (CheckTwoBytePrefix(TimerOp1, TimerOp2, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // TimerOp              := 0x5B 0x33

        const ByteData TimerOp1 = 0x5B;
        const ByteData TimerOp2 = 0x33;

        // DefToBCD             := ToBCDOp Operand Target

        public class DefToBCD : AmlParserNode
        {
            public Operand operand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefToBCD(out DefToBCD result, ref int offset)
        {
            int offset2 = offset;
            result = new DefToBCD();
            if (CheckTwoBytePrefix(ToBCDOp1, ToBCDOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseOperand (out result.operand, ref offset2) == Failure ||
                ParseTarget   (out result.target,  ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // ToBCDOp              := ExtOpPrefix 0x29

        const ByteData ToBCDOp1 = ExtOpPrefix;
        const ByteData ToBCDOp2 = 0x29;

        // DefToBuffer          := ToBufferOp Operand Target

        public class DefToBuffer : AmlParserNode
        {
            public Operand operand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefToBuffer(out DefToBuffer result, ref int offset)
        {
            int offset2 = offset;
            result = new DefToBuffer();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ToBufferOp) {
                return Failure;
            }
            if (ParseOperand (out result.operand, ref offset2) == Failure ||
                ParseTarget   (out result.target,  ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // ToBufferOp           := 0x96

        const ByteData ToBufferOp = 0x96;

        // DefToDecimalString   := ToDecimalStringOp Operand Target

        public class DefToDecimalString : AmlParserNode
        {
            public Operand operand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefToDecimalString(out DefToDecimalString result, ref int offset)
        {
            int offset2 = offset;
            result = new DefToDecimalString();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ToDecimalStringOp) {
                return Failure;
            }
            if (ParseOperand (out result.operand, ref offset2) == Failure ||
                ParseTarget   (out result.target,  ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }
        
        // ToDecimalStringOp    := 0x97

        const ByteData ToDecimalStringOp = 0x97;

        // DefToHexString       := ToHexStringOp Operand Target

        public class DefToHexString : AmlParserNode
        {
            public Operand operand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefToHexString(out DefToHexString result, ref int offset)
        {
            int offset2 = offset;
            result = new DefToHexString();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ToHexStringOp) {
                return Failure;
            }
            if (ParseOperand (out result.operand, ref offset2) == Failure ||
                ParseTarget   (out result.target,  ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // ToHexStringOp        := 0x98

        const ByteData ToHexStringOp = 0x98;

        // DefToInteger         := ToIntegerOp Operand Target

        public class DefToInteger : AmlParserNode
        {
            public Operand operand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefToInteger(out DefToInteger result, ref int offset)
        {
            int offset2 = offset;
            result = new DefToInteger();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ToIntegerOp) {
                return Failure;
            }
            if (ParseOperand (out result.operand, ref offset2) == Failure ||
                ParseTarget   (out result.target,  ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // ToIntegerOp          := 0x99

        const ByteData ToIntegerOp = 0x99;

        // DefToString          := ToStringOp TermArg LengthArg Target

        public class DefToString : AmlParserNode
        {
            public TermArg termArg;
            public LengthArg lengthArg;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefToString(out DefToString result, ref int offset)
        {
            int offset2 = offset;
            result = new DefToString();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != ToStringOp) {
                return Failure;
            }
            if (ParseTermArg  (out result.termArg,  ref offset2) == Failure ||
                ParseLengthArg(out result.lengthArg, ref offset2) == Failure ||
                ParseTarget   (out result.target,    ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // LengthArg            := TermArg => Integer

        public class LengthArg : AmlParserNode
        {
            public TermArg integer;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseLengthArg(out LengthArg result, ref int offset)
        {
            int offset2 = offset;
            result = new LengthArg();

            if (ParseTermArg(out result.integer, ref offset2) == Failure /*||
                !TermArgEvaluatesTo(result.integer, TermArgType.Integer)*/) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // ToStringOp           := 0x9C

        const ByteData ToStringOp = 0x9C;

        // DefWait              := WaitOp EventObject Operand

        public class DefWait : AmlParserNode
        {
            public EventObject eventObject;
            public Operand operand;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefWait(out DefWait result, ref int offset)
        {
            int offset2 = offset;
            result = new DefWait();
            if (CheckTwoBytePrefix(WaitOp1, WaitOp2, ref offset2) == Failure) {
                return Failure;
            }

            if (ParseEventObject(out result.eventObject, ref offset2) == Failure ||
                ParseOperand    (out result.operand,     ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // WaitOp               := ExtOpPrefix 0x25

        const ByteData WaitOp1 = ExtOpPrefix;
        const ByteData WaitOp2 = 0x25;

        // DefXOr               := XorOp Operand Operand Target

        public class DefXOr : AmlParserNode
        {
            public Operand leftOperand;
            public Operand rightOperand;
            public Target target;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDefXOr(out DefXOr result, ref int offset)
        {
            int offset2 = offset;
            result = new DefXOr();
            ByteData prefix = stream.ReadByteData(ref offset2);
            if (prefix != XorOp) {
                return Failure;
            }
            if (ParseOperand(out result.leftOperand, ref offset2) == Failure ||
                ParseOperand(out result.rightOperand, ref offset2) == Failure ||
                ParseTarget (out result.target,       ref offset2) == Failure) {
                return Failure;
            }
            offset = offset2;
            return Success;
        }

        // XorOp                := 0x7F

        const ByteData XorOp = 0x7F;


        //
        // Section 18.2.6: Miscellaneous Objects Encoding
        //

        //
        // Section 18.2.6.1: Arg Objects Encoding
        //

        // ArgObj               := Arg0Op | Arg1Op | Arg2Op | Arg3Op | Arg4Op |
        //                         Arg5Op | Arg6Op

        public class ArgObj : AmlParserNode
        {
            public ByteData op;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseArgObj(out ArgObj result, ref int offset)
        {
            int offset2 = offset;
            result = new ArgObj();
            ByteData op = stream.ReadByteData(ref offset2);
            if (op != Arg0Op &&
                op != Arg1Op &&
                op != Arg2Op &&
                op != Arg3Op &&
                op != Arg4Op &&
                op != Arg5Op &&
                op != Arg6Op) {
                return Failure;
            }
            result.op = (ByteData)(op - Arg0Op);
            offset = offset2;
            return Success;
        }

        // Arg0Op               := 0x68

        const ByteData Arg0Op = 0x68;

        // Arg1Op               := 0x69

        const ByteData Arg1Op = 0x69;

        // Arg2Op               := 0x6A

        const ByteData Arg2Op = 0x6A;

        // Arg3Op               := 0x6B

        const ByteData Arg3Op = 0x6B;

        // Arg4Op               := 0x6C

        const ByteData Arg4Op = 0x6C;

        // Arg5Op               := 0x6D

        const ByteData Arg5Op = 0x6D;

        // Arg6Op               := 0x6E


        const ByteData Arg6Op = 0x6E;

        //
        // Section 18.2.6.2: Local Objects Encoding
        //

        // LocalObj             := Local0Op | Local1Op | Local2Op | Local3Op | Local4Op |
        //                         Local5Op | Local6Op | Local7Op

        public class LocalObj : AmlParserNode
        {
            public ByteData op;
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseLocalObj(out LocalObj result, ref int offset)
        {
            int offset2 = offset;
            result = new LocalObj();
            ByteData op = stream.ReadByteData(ref offset2);
            if (op != Local0Op &&
                op != Local1Op &&
                op != Local2Op &&
                op != Local3Op &&
                op != Local4Op &&
                op != Local5Op &&
                op != Local6Op &&
                op != Local7Op) {
                return Failure;
            }
            result.op = (ByteData)(op - Local0Op);
            offset = offset2;
            return Success;
        }

        // Local0Op             := 0x60

        const ByteData Local0Op = 0x60;

        // Local1Op             := 0x61

        const ByteData Local1Op = 0x61;

        // Local2Op             := 0x62

        const ByteData Local2Op = 0x62;

        // Local3Op             := 0x63

        const ByteData Local3Op = 0x63;

        // Local4Op             := 0x64

        const ByteData Local4Op = 0x64;

        // Local5Op             := 0x65

        const ByteData Local5Op = 0x65;

        // Local6Op             := 0x66

        const ByteData Local6Op = 0x66;

        // Local7Op             := 0x67

        const ByteData Local7Op = 0x67;

        //
        // Section 18.2.6.3: Debug Objects Encoding
        //

        // DebugObj             := DebugOp

        public class DebugObj : AmlParserNode
        {
            // No data
            
            public override void Accept(AmlParserNodeVisitor v)
            {
                v.Visit(this);
            }
        }

        private ParseSuccess ParseDebugObj(out DebugObj result, ref int offset)
        {
            int offset2 = offset;
            result = new DebugObj();
            if (CheckTwoBytePrefix(DebugOp1, DebugOp2, ref offset2) == Failure) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }

        // DebugOp              := ExtOpPrefix 0x31

        const ByteData DebugOp1 = ExtOpPrefix;
        const ByteData DebugOp2 = 0x31;

        // Helpers

        private ParseSuccess CheckTwoBytePrefix(byte op1, byte op2, ref int offset) {
            int offset2 = offset;
            ByteData prefix1, prefix2;

            prefix1 = stream.ReadByteData(ref offset2);
            if (prefix1 != op1) {
                return Failure;
            }

            prefix2 = stream.ReadByteData(ref offset2);

            if (prefix2 != op2) {
                return Failure;
            }

            offset = offset2;
            return Success;
        }
    }
}
