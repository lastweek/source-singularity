//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.Collections;
using System.IO;
using Bartok.DebugInfo;

namespace Bartok.MSIL
{

  public class Instruction {

      // Constructor Methods

      internal static Instruction[] getInstructions(MetaDataLoader mdLoader,
                                                    Stream fileStream,
                                                    int codeOffset,
                                                    int[] lines,
                                                    int[] columns,
                                                    int[] offsets,
                                                    String srcFileName,
                                                    int lineCount,
                                                    out EHClause[] ehTable,
                                                    out int[] bbTable,
                                                    out int maxStack,
                                                    out Signature.Type[] locals,
                                                    out bool initLocals) {
          fileStream.Seek(codeOffset, SeekOrigin.Begin);
          BinaryReader reader = new BinaryReader(fileStream);
          byte headerByte       = reader.ReadByte();
          byte formatMask = (byte) (headerByte & 0x7);
          int codeSize;
          byte[] codeBytes;
          ehTable = sharedEmptyTable;
          switch ((MethodFormats) formatMask) {
            case MethodFormats.Tiny:
            case MethodFormats.Tiny1: {
                initLocals = false;
                maxStack = 8;
                codeSize = headerByte >> 2;
                locals = null;
                codeBytes = new byte[codeSize];
                int count = reader.Read(codeBytes, 0, codeSize);
                if (count != codeSize) {
                    throw new IllegalInstructionStreamException("Only got "+count+" out of "+codeSize+" code bytes");
                }
                break;
            }
            case MethodFormats.Fat: {
                // for Fat format, check for CorILMethod_InitLocals
                // Section 24.4.4 of ECMA spec, partition II
                initLocals = ((headerByte & 0x10) != 0);
                byte headerByte2 = reader.ReadByte();
                int size = headerByte2 >> 4;
                if (size != 3) {
                    throw new IllegalInstructionStreamException("Unexpected FAT size: "+size);
                }
                maxStack = reader.ReadUInt16();
                codeSize = reader.ReadInt32();
                int localVarSignatureToken = reader.ReadInt32();
                if (localVarSignatureToken == 0) {
                    locals = null;
                }
                else {
                    MetaDataStandAloneSig standAloneSig =
                        (MetaDataStandAloneSig)
                        mdLoader.getObjectFromToken(localVarSignatureToken);
                    Signature unresolvedSignature = standAloneSig.Signature;
                    SignatureLocalVar localVarSignature = (SignatureLocalVar)
                        unresolvedSignature.resolve(mdLoader);
                    locals = localVarSignature.Locals;
                }
                codeBytes = new byte[codeSize];
                int count = reader.Read(codeBytes, 0, codeSize);
                if (count != codeSize) {
                    throw new IllegalInstructionStreamException("Only got "+count+" out of "+codeSize+" code bytes");
                }
                break;
            }
            default: {
                throw new IllegalInstructionStreamException("Unknown format: "+formatMask.ToString("x"));
            }
          }
          int pcLimit = codeBytes.Length;
          int[] byteToInstrMapping = new int[pcLimit+1];
          int instructionCount = 0;
          int instructionLength, operandLength;
          for (int pc = 0; pc < pcLimit; pc += instructionLength + operandLength) {
              byteToInstrMapping[pc] = instructionCount;
              instructionCount++;
              Opcode opcode = (Opcode) codeBytes[pc];
              switch (opcode) {
                case Opcode.PREFIX1:
                    instructionLength = 2;
                    opcode = (Opcode) (codeBytes[pc+1] + 256);
                    if (opcode < 0 || (Opcode) opcode >= Opcode.COUNT) {
                        throw new IllegalInstructionStreamException("Saw prefixed opcode of "+opcode);
                    }
                    break;
                case Opcode.PREFIXREF:
                case Opcode.PREFIX2:
                case Opcode.PREFIX3:
                case Opcode.PREFIX4:
                case Opcode.PREFIX5:
                case Opcode.PREFIX6:
                case Opcode.PREFIX7:
                    throw new IllegalInstructionStreamException("Saw unexpected prefix opcode "+opcode);
                default:
                    instructionLength = 1;
                    break;
              }
              OpcodeInfo opcodeInfo = opcodeInfoTable[(int) opcode];
              operandLength = opcodeInfo.operandSize;
              if (operandLength == 0xFF) {
                  int operandOffset = pc + instructionLength;
                  switch (opcodeInfo.operandFormat) {
                    case OperandFormat.Switch: {
                        int caseCount =
                            intFromCodeBytes(codeBytes, operandOffset);
                        operandLength = 4 + 4 * caseCount;
                        break;
                    }
                    case OperandFormat.InlinePhi: {
                        int caseCount = codeBytes[operandOffset];
                        operandLength = 1 + 2 * caseCount;
                        break;
                    }
                    case OperandFormat.BranchTarget: {
                        int byteCount =
                            intFromCodeBytes(codeBytes, operandOffset);
                        operandLength = 4 + byteCount;
                        break;
                    }
                    case OperandFormat.ShortBranchTarget: {
                        int byteCount = codeBytes[operandOffset];
                        operandLength = 1 + byteCount;
                        break;
                    }
                    default:
                        throw new IllegalInstructionStreamException("Unexpected operand format "+opcodeInfo.operandFormat);
                  }
              }
          }
          byteToInstrMapping[pcLimit] = instructionCount;
          BitArray bbStarts = new BitArray(instructionCount+1);
          // Check whether or not there is an EH section
          if (formatMask == (byte) MethodFormats.Fat &&
              (headerByte & 0x08) != 0) {
              int sectionPadding = (codeOffset + codeSize) % 4;
              if (sectionPadding != 0) {
                  while (sectionPadding < 4) {
                      sectionPadding++;
                      byte padding = reader.ReadByte();
                  }
              }
              byte sectionKind = reader.ReadByte();
              if ((sectionKind & 0x80) != 0) {
                  throw new IllegalInstructionStreamException("More than one section after the code");
              }
              if ((sectionKind & 0x3f) != (int) SectionKind.EHTable) {
                  throw new IllegalInstructionStreamException("Expected EH table section, got "+sectionKind.ToString("x"));
              }
              int dataSize;
              if ((sectionKind & 0x40) == 0) {
                  // Small section
                  int ehByteCount = reader.ReadByte();
                  dataSize = (ehByteCount) / 12;
                  int headerSize = (ehByteCount % 12);
                  if ((headerSize != 0) && (headerSize != 4)) {
                      throw new IllegalInstructionStreamException("Unexpected byte count for small EH table: "+ehByteCount);
                  }
                  int sectSmallReserved = reader.ReadInt16();
                  ehTable = new EHClause[dataSize];
                  for (int i = 0; i < dataSize; i++) {
                      int flags         = reader.ReadUInt16();
                      int tryOffset     = reader.ReadUInt16();
                      int tryLength     = reader.ReadByte();
                      int handlerOffset = reader.ReadUInt16();
                      int handlerLength = reader.ReadByte();
                      int tokenOrOffset =
                          (i+1==dataSize &&
                           headerSize==0 &&
                           flags != (int) EHClause.ExceptionFlag.None) ?
                          0 :   // The VC++ compiler did not output a 0 here!
                          reader.ReadInt32();
                      int tryInstrOffset =
                          byteToInstrMapping[tryOffset];
                      bbStarts[tryInstrOffset] =true;
                      int tryInstrEnd =
                          byteToInstrMapping[tryOffset + tryLength];
                      int handlerInstrOffset =
                          byteToInstrMapping[handlerOffset];
                      bbStarts[handlerInstrOffset] = true;
                      int handlerInstrEnd =
                          byteToInstrMapping[handlerOffset + handlerLength];
                      bbStarts[handlerInstrEnd] = true;
                      MetaDataObject classObject = null;
                      if ((flags & (int) EHClause.ExceptionFlag.Filter) != 0) {
                          tokenOrOffset = byteToInstrMapping[tokenOrOffset];
                          bbStarts[tokenOrOffset] = true;
                      }
                      else if (flags == (int) EHClause.ExceptionFlag.None) {
                          classObject =
                              mdLoader.getObjectFromToken(tokenOrOffset);
                          tokenOrOffset = 0;
                      }
                      else {
                          // The VC++ compiler is known to get the ehByteCount
                          // wrong and generate spurious data for tokenOrOffset
                          if (headerSize != 0 && tokenOrOffset != 0) {
                              Console.WriteLine("Unknown token or offset "+tokenOrOffset.ToString("x8"));
                          }
                      }
                      ehTable[i] =
                          new EHClause(flags,
                                       tryInstrOffset,
                                       tryInstrEnd - tryInstrOffset,
                                       handlerInstrOffset,
                                       handlerInstrEnd - handlerInstrOffset,
                                       tokenOrOffset, classObject);
                  }
              }
              else {
                  // Fat section
                  int ehByteCount;
                  ehByteCount = reader.ReadByte();
                  ehByteCount |= reader.ReadByte() << 8;
                  ehByteCount |= reader.ReadByte() << 16;
                  dataSize = ehByteCount / 24;
                  int headerSize = (ehByteCount % 12);
                  if ((headerSize != 0) && (headerSize != 4)) {
                      throw new IllegalInstructionStreamException("Unexpected byte count for fat EH table: "+ehByteCount);
                  }
                  ehTable = new EHClause[dataSize];
                  for (int i = 0; i < dataSize; i++) {
                      int flags         = reader.ReadInt32();
                      int tryOffset     = reader.ReadInt32();
                      int tryLength     = reader.ReadInt32();
                      int handlerOffset = reader.ReadInt32();
                      int handlerLength = reader.ReadInt32();
                      int tokenOrOffset = reader.ReadInt32();
                      int tryInstrOffset =
                          byteToInstrMapping[tryOffset];
                      bbStarts[tryInstrOffset] = true;
                      int tryInstrEnd =
                          byteToInstrMapping[tryOffset + tryLength];
                      int handlerInstrOffset =
                          byteToInstrMapping[handlerOffset];
                      bbStarts[handlerInstrOffset] = true;
                      int handlerInstrEnd =
                          byteToInstrMapping[handlerOffset + handlerLength];
                      bbStarts[handlerInstrEnd] = true;
                      MetaDataObject classObject = null;
                      if ((flags & (int) EHClause.ExceptionFlag.Filter) != 0) {
                          tokenOrOffset = byteToInstrMapping[tokenOrOffset];
                          bbStarts[tokenOrOffset] = true;
                      }
                      else if (flags == (int) EHClause.ExceptionFlag.None) {
                          classObject =
                              mdLoader.getObjectFromToken(tokenOrOffset);
                          tokenOrOffset = 0;
                      }
                      else {
                          // The VC++ compiler is known to get the ehByteCount
                          // wrong and generate spurious data for tokenOrOffset
                          if (headerSize != 0 && tokenOrOffset != 0) {
                              Console.WriteLine("Unknown token or offset "+tokenOrOffset.ToString("x8"));
                          }
                      }
                      ehTable[i] =
                          new EHClause(flags,
                                       tryInstrOffset,
                                       tryInstrEnd - tryInstrOffset,
                                       handlerInstrOffset,
                                       handlerInstrEnd - handlerInstrOffset,
                                       tokenOrOffset, classObject);
                  }
              }
          }
          Instruction[] instructionTable = new Instruction[instructionCount];
          int instructionCounter = 0;
          int currLineIndex = 0;
          int prevLineNumber = 0;
          DebugLineNumber lineInfo = null;
          for (int pc = 0; pc < pcLimit;) {
              if (pc > 0 && byteToInstrMapping[pc] == 0) {
                  throw new IllegalInstructionStreamException("Out of sync at "+pc.ToString("x"));
              }
              // read in the line number information.
              int lineNumber = 0;
              int column = 0;
              if (lineCount != 0) {
                  if (currLineIndex == lineCount - 1) {
                      // last line.
                      lineNumber = lines[currLineIndex];
                  }
                  else {
                      int nextOffset = offsets[currLineIndex+1];
                      if (pc < nextOffset) {
                          lineNumber = lines[currLineIndex];
                          column = columns[currLineIndex];
                      }
                      else if (pc == nextOffset) {
                          // advance to next line record
                          currLineIndex++;
                          lineNumber = lines[currLineIndex];
                          column = columns[currLineIndex];
                      }
                      else {
                          Console.WriteLine("Error! Reading lineNumber");
                      }
                  }
              }
              Opcode opcode = (Opcode) codeBytes[pc];
              pc++;
              if (opcode == Opcode.PREFIX1) {
                  opcode = (Opcode) (codeBytes[pc] + 256);
                  pc++;
              }
              OpcodeInfo opcodeInfo = opcodeInfoTable[(int) opcode];
              Operand operand;

              switch (opcodeInfo.operandFormat) {
                case OperandFormat.None:
                    if (opcode == Opcode.RET || opcode == Opcode.THROW
                        || opcode == Opcode.RETHROW
                        || opcode == Opcode.ENDFINALLY
                        || opcode == Opcode.ENDFILTER) {
                        // mark the instruction after a throw, return, or
                        // endfinally as the beginning of a basic block.
                        //
                        // If we have dead code, then there may be no branch to
                        // it.
                        if (pc < pcLimit) {
                            bbStarts[byteToInstrMapping[pc]] = true;
                        }
                    }
                    operand = null;
                    break;
                case OperandFormat.Var:
                    operand =
                        new OperandInt(shortFromCodeBytes(codeBytes, pc));
                    pc += 2;
                    break;
                case OperandFormat.Int:
                case OperandFormat.RVA:
                    operand = new OperandInt(intFromCodeBytes(codeBytes, pc));
                    pc += 4;
                    break;
                case OperandFormat.Float:
                    operand =
                        new OperandDouble(doubleFromCodeBytes(codeBytes, pc));
                    pc += 8;
                    break;
                case OperandFormat.BranchTarget: {
                    int target = intFromCodeBytes(codeBytes, pc);
                    pc += 4;
                    if (opcodeInfo.operandSize == 0xFF) {
                        // Random data inserted into instruction stream
                        byte[] dataBuffer = new byte[target];
                        Array.Copy(codeBytes, pc, dataBuffer, 0, target);
                        pc += target;
                        operand = new OperandByteArray(dataBuffer);
                    }
                    else {
                        // A real branch target
                        int instrTarget = byteToInstrMapping[pc+target];
                        bbStarts[instrTarget] = true;
                        // Fall through branch should be marked too
                        bbStarts[instructionCounter+1] = true;
                        operand = new OperandTarget(instrTarget);
                    }
                    break;
                }
                case OperandFormat.Int8:
                    operand =
                        new OperandLong(longFromCodeBytes(codeBytes, pc));
                    pc += 8;
                    break;
                case OperandFormat.Method: {
                    int token = intFromCodeBytes(codeBytes, pc);
                    pc += 4;
                    MetaDataObject mdMethod =
                        mdLoader.getObjectFromToken(token);
                    operand = new OperandObject(mdMethod);
                    break;
                }
                case OperandFormat.Field: {
                    int token = intFromCodeBytes(codeBytes, pc);
                    pc += 4;
                    int index = token & 0x00FFFFFF;
                    MetaDataObject mdField =
                        mdLoader.getObjectFromToken(token);
                    operand = new OperandObject(mdField);
                    break;
                }
                case OperandFormat.Type: {
                    int token = intFromCodeBytes(codeBytes, pc);
                    pc += 4;
                    MetaDataObject type = mdLoader.getObjectFromToken(token);
                    operand = new OperandObject(type);
                    break;
                }
                case OperandFormat.Token: {
                    int token = intFromCodeBytes(codeBytes, pc);
                    pc += 4;
                    MetaDataObject mdToken =
                        mdLoader.getObjectFromToken(token);
                    operand = new OperandObject(mdToken);
                    break;
                }
                case OperandFormat.String: {
                    int token = intFromCodeBytes(codeBytes, pc);
                    pc += 4;
                    if (((uint) token & 0xFF000000) != (uint) MetaDataLoader.TokenType.String) {
                        throw new IllegalInstructionStreamException("Unexpected string token "+token.ToString("x"));
                    }
                    int index = token & 0x00FFFFFF;
                    operand = new OperandString(mdLoader.getUserString(index));
                    break;
                }
                case OperandFormat.Sig: {
                    int token = intFromCodeBytes(codeBytes, pc);
                    pc += 4;
                    MetaDataObject calleeDescr =
                        mdLoader.getObjectFromToken(token);
                    operand = new OperandObject(calleeDescr);
                    break;
                }
                case OperandFormat.Switch: {
                    int caseCount = intFromCodeBytes(codeBytes, pc);
                    pc += 4;
                    int[] branchArray = new int[caseCount];
                    int nextPC = pc + 4 * caseCount;
                    for (int j = 0; j < caseCount; j++) {
                        int target = intFromCodeBytes(codeBytes, pc);
                        pc += 4;
                        int instrTarget = byteToInstrMapping[nextPC+target];
                        bbStarts[instrTarget] = true;
                        branchArray[j] = instrTarget;
                    }
                    bbStarts[instructionCounter+1] = true; // Fall through
                    operand = new OperandTargetArray(branchArray);
                    break;
                }
                case OperandFormat.InlinePhi: {
                    int caseCount = codeBytes[pc];
                    pc++;
                    byte[] varArray = new byte[caseCount];
                    for (int j = 0; j < caseCount; j++) {
                        varArray[j] = codeBytes[pc];
                        pc++;
                    }
                    operand = new OperandByteArray(varArray);
                    break;
                }
                case OperandFormat.ShortVar:
                    operand = new OperandInt(codeBytes[pc]);
                    pc++;
                    break;
                case OperandFormat.ShortInt: {
                    int value = codeBytes[pc];
                    pc++;
                    if (value > 127) {
                        value = -(256-value);
                    }
                    operand = new OperandInt(value);
                    break;
                }
                case OperandFormat.ShortFloat:
                    operand =
                        new OperandSingle(singleFromCodeBytes(codeBytes, pc));
                    pc += 4;
                    break;
                case OperandFormat.ShortBranchTarget: {
                    int offset = codeBytes[pc];
                    pc++;
                    if (offset > 127) {
                        offset = -(256-offset);
                    }
                    int instrTarget = byteToInstrMapping[pc+offset];
                    bbStarts[instrTarget] = true;
                    // Fall through branch should be marked too
                    bbStarts[instructionCounter+1] = true;
                    operand = new OperandTarget(instrTarget);
                    break;
                }
                default:
                    throw new IllegalInstructionStreamException("Unknown operand type "+opcodeInfo.operandFormat);
              }
              if (lineNumber != prevLineNumber && srcFileName != null) {
                      lineInfo = new CVLineNumber(lineNumber,
                                                  column,
                                                  srcFileName);
                  prevLineNumber = lineNumber;
              }
              instructionTable[instructionCounter] =
                  new Instruction(opcode, operand, lineInfo);
              instructionCounter++;
          }
          int bbCount = 1;
          for (int i = 1; i < instructionCount; i++) {
              if (bbStarts[i]) {
                  bbCount++;
              }
          }
          bbTable = new int[bbCount];
          bbCount = 1;
          for (int i = 1; i < instructionCount; i++) {
              if (bbStarts[i]) {
                  bbTable[bbCount] = i;
                  bbCount++;
              }
          }
          return instructionTable;
      }

      private Instruction(Opcode opcode, Operand operand,
                          DebugLineNumber lineNumber) {
          this.opcode = opcode;
          this.operand = operand;
          this.lineNumber = lineNumber;
      }

      // Access Methods

      public Opcode Operator {
          get {
              return this.opcode;
          }
      }

      public Operand Argument {
          get {
              return this.operand;
          }
      }

      public DebugLineNumber LineNumber {
          get {
              return this.lineNumber;
          }
      }

      public bool isControl() {
          return opcodeInfoTable[(int) this.opcode].isControl;
      }

      // Helper Methods

      private static int intFromCodeBytes(byte[] codeBytes, int offset) {
          return ((codeBytes[offset]) |
                  (codeBytes[offset+1] << 8) |
                  (codeBytes[offset+2] << 16) |
                  (codeBytes[offset+3] << 24));
      }

      private static short shortFromCodeBytes(byte[] codeBytes, int offset) {
          return (short) ((codeBytes[offset]) |
                          (codeBytes[offset+1] << 8));
      }

      private static long longFromCodeBytes(byte[] codeBytes, int offset) {
          return (((long) ((uint) (codeBytes[offset]) |
                           (uint) (codeBytes[offset+1] << 8) |
                           (uint) (codeBytes[offset+2] << 16) |
                           (uint) (codeBytes[offset+3] << 24))) |
                  (((long) ((uint) (codeBytes[offset+4]) |
                           (uint) (codeBytes[offset+5] << 8) |
                           (uint) (codeBytes[offset+6] << 16) |
                           (uint) (codeBytes[offset+7] << 24))) << 32));
      }

      private static float singleFromCodeBytes(byte[] codeBytes, int offset) {
          MemoryStream memoryStream = new MemoryStream(codeBytes, offset, 4);
          BinaryReader binaryReader = new BinaryReader(memoryStream);
          return binaryReader.ReadSingle();
      }

      private static double doubleFromCodeBytes(byte[] codeBytes, int offset) {
          MemoryStream memoryStream = new MemoryStream(codeBytes, offset, 8);
          BinaryReader binaryReader = new BinaryReader(memoryStream);
          return binaryReader.ReadDouble();
      }

      // Debug Methods

      public override String ToString() {
          if (lineNumber != null) {
              return (opcodeInfoTable[(int) this.opcode].name +
                      lineNumber.ToString());
          }
          else {
              return (opcodeInfoTable[(int) this.opcode].name);
          }
      }

      internal static void dumpToConsole(Instruction[] instructions) {
          int count = instructions.Length;
          for (int i = 0; i < count; i++) {
              Console.WriteLine("IL_"+i.ToString("x4")+":  "+instructions[i]);
          }
      }

      // State

      private readonly Opcode opcode;
      private readonly Operand operand;
      private readonly DebugLineNumber lineNumber;

      // Internal Types

      private enum MethodFormats: byte {
          Tiny = 2,
              Fat = 3,
              Tiny1 = 6
      }

      private enum SectionKind: byte {
          Reserved = 0,
              EHTable = 1,
              OptILTable = 2
      }

      public enum Opcode: short {
          NOP,
              BREAK,
              LDARG_0,
              LDARG_1,
              LDARG_2,
              LDARG_3,
              LDLOC_0,
              LDLOC_1,
              LDLOC_2,
              LDLOC_3,
              STLOC_0,
              STLOC_1,
              STLOC_2,
              STLOC_3,
              LDARG_S,
              LDARGA_S,
              STARG_S,
              LDLOC_S,
              LDLOCA_S,
              STLOC_S,
              LDNULL,
              LDC_I4_M1,
              LDC_I4_0,
              LDC_I4_1,
              LDC_I4_2,
              LDC_I4_3,
              LDC_I4_4,
              LDC_I4_5,
              LDC_I4_6,
              LDC_I4_7,
              LDC_I4_8,
              LDC_I4_S,
              LDC_I4,
              LDC_I8,
              LDC_R4,
              LDC_R8,
              UNUSED49,
              DUP,
              POP,
              JMP,
              CALL,
              CALLI,
              RET,
              BR_S,
              BRFALSE_S,
              BRTRUE_S,
              BEQ_S,
              BGE_S,
              BGT_S,
              BLE_S,
              BLT_S,
              BNE_UN_S,
              BGE_UN_S,
              BGT_UN_S,
              BLE_UN_S,
              BLT_UN_S,
              BR,
              BRFALSE,
              BRTRUE,
              BEQ,
              BGE,
              BGT,
              BLE,
              BLT,
              BNE_UN,
              BGE_UN,
              BGT_UN,
              BLE_UN,
              BLT_UN,
              SWITCH,
              LDIND_I1,
              LDIND_U1,
              LDIND_I2,
              LDIND_U2,
              LDIND_I4,
              LDIND_U4,
              LDIND_I8,
              LDIND_I,
              LDIND_R4,
              LDIND_R8,
              LDIND_REF,
              STIND_REF,
              STIND_I1,
              STIND_I2,
              STIND_I4,
              STIND_I8,
              STIND_R4,
              STIND_R8,
              ADD,
              SUB,
              MUL,
              DIV,
              DIV_UN,
              REM,
              REM_UN,
              AND,
              OR,
              XOR,
              SHL,
              SHR,
              SHR_UN,
              NEG,
              NOT,
              CONV_I1,
              CONV_I2,
              CONV_I4,
              CONV_I8,
              CONV_R4,
              CONV_R8,
              CONV_U4,
              CONV_U8,
              CALLVIRT,
              CPOBJ,
              LDOBJ,
              LDSTR,
              NEWOBJ,
              CASTCLASS,
              ISINST,
              CONV_R_UN,
              ANN_DATA_S,
              UNUSED1,
              UNBOX,
              THROW,
              LDFLD,
              LDFLDA,
              STFLD,
              LDSFLD,
              LDSFLDA,
              STSFLD,
              STOBJ,
              CONV_OVF_I1_UN,
              CONV_OVF_I2_UN,
              CONV_OVF_I4_UN,
              CONV_OVF_I8_UN,
              CONV_OVF_U1_UN,
              CONV_OVF_U2_UN,
              CONV_OVF_U4_UN,
              CONV_OVF_U8_UN,
              CONV_OVF_I_UN,
              CONV_OVF_U_UN,
              BOX,
              NEWARR,
              LDLEN,
              LDELEMA,
              LDELEM_I1,
              LDELEM_U1,
              LDELEM_I2,
              LDELEM_U2,
              LDELEM_I4,
              LDELEM_U4,
              LDELEM_I8,
              LDELEM_I,
              LDELEM_R4,
              LDELEM_R8,
              LDELEM_REF,
              STELEM_I,
              STELEM_I1,
              STELEM_I2,
              STELEM_I4,
              STELEM_I8,
              STELEM_R4,
              STELEM_R8,
              STELEM_REF,
              LDELEM,
              STELEM,
              UNBOX_ANY,
              UNUSED5,
              UNUSED6,
              UNUSED7,
              UNUSED8,
              UNUSED9,
              UNUSED10,
              UNUSED11,
              UNUSED12,
              UNUSED13,
              UNUSED14,
              UNUSED15,
              UNUSED16,
              UNUSED17,
              CONV_OVF_I1,
              CONV_OVF_U1,
              CONV_OVF_I2,
              CONV_OVF_U2,
              CONV_OVF_I4,
              CONV_OVF_U4,
              CONV_OVF_I8,
              CONV_OVF_U8,
              UNUSED50,
              UNUSED18,
              UNUSED19,
              UNUSED20,
              UNUSED21,
              UNUSED22,
              UNUSED23,
              REFANYVAL,
              CKFINITE,
              UNUSED24,
              UNUSED25,
              MKREFANY,
              ANN_CALL,
              ANN_CATCH,
              ANN_DEAD,
              ANN_HOISTED,
              ANN_HOISTED_CALL,
              ANN_LAB,
              ANN_DEF,
              ANN_REF_S,
              ANN_PHI,
              LDTOKEN,
              CONV_U2,
              CONV_U1,
              CONV_I,
              CONV_OVF_I,
              CONV_OVF_U,
              ADD_OVF,
              ADD_OVF_UN,
              MUL_OVF,
              MUL_OVF_UN,
              SUB_OVF,
              SUB_OVF_UN,
              ENDFINALLY,
              LEAVE,
              LEAVE_S,
              STIND_I,
              CONV_U,
              UNUSED26,
              UNUSED27,
              UNUSED28,
              UNUSED29,
              UNUSED30,
              UNUSED31,
              UNUSED32,
              UNUSED33,
              UNUSED34,
              UNUSED35,
              UNUSED36,
              UNUSED37,
              UNUSED38,
              UNUSED39,
              UNUSED40,
              UNUSED41,
              UNUSED42,
              UNUSED43,
              UNUSED44,
              UNUSED45,
              UNUSED46,
              UNUSED47,
              UNUSED48,
              PREFIX7,
              PREFIX6,
              PREFIX5,
              PREFIX4,
              PREFIX3,
              PREFIX2,
              PREFIX1,
              PREFIXREF,
              ARGLIST,
              CEQ,
              CGT,
              CGT_UN,
              CLT,
              CLT_UN,
              LDFTN,
              LDVIRTFTN,
              UNUSED56,
              LDARG,
              LDARGA,
              STARG,
              LDLOC,
              LDLOCA,
              STLOC,
              LOCALLOC,
              UNUSED57,
              ENDFILTER,
              UNALIGNED,
              VOLATILE,
              TAILCALL,
              INITOBJ,
              ANN_LIVE,
              CPBLK,
              INITBLK,
              ANN_REF,
              RETHROW,
              UNUSED51,
              SIZEOF,
              REFANYTYPE,
              UNUSED52,
              UNUSED53,
              UNUSED54,
              UNUSED55,
              ANN_DATA,
              ILLEGAL,
              MACRO_END,
              COUNT
      }

      private enum OperandFormat: byte {
          None                  = 0,
              Var               = 1,
              Int               = 2,
              Float             = 3,
              BranchTarget      = 4,
              Int8              = 5,
              Method            = 6,
              Field             = 7,
              Type              = 8,
              String            = 9,
              Sig               = 10,
              RVA               = 11,
              Token             = 12,
              Switch            = 13,
              InlinePhi         = 14,
              PrimaryMask       = (ShortOperand-1),
              ShortOperand      = 16,
              Opcode            = (ShortOperand + None),
              ShortVar          = (ShortOperand + Var),
              ShortInt          = (ShortOperand + Int),
              ShortFloat        = (ShortOperand + Float),
              ShortBranchTarget = (ShortOperand + BranchTarget),
              Illegal           = 0Xff
      }

      private static readonly EHClause[] sharedEmptyTable = new EHClause[0];

      private static readonly OpcodeInfo[] opcodeInfoTable = new OpcodeInfo[(int) Opcode.COUNT] {
         new OpcodeInfo("nop",Opcode.NOP,OperandFormat.None,0,false),
         new OpcodeInfo("break",Opcode.BREAK,OperandFormat.None,0,false),
         new OpcodeInfo("ldarg.0",Opcode.LDARG_0,OperandFormat.None,0,false),
         new OpcodeInfo("ldarg.1",Opcode.LDARG_1,OperandFormat.None,0,false),
         new OpcodeInfo("ldarg.2",Opcode.LDARG_2,OperandFormat.None,0,false),
         new OpcodeInfo("ldarg.3",Opcode.LDARG_3,OperandFormat.None,0,false),
         new OpcodeInfo("ldloc.0",Opcode.LDLOC_0,OperandFormat.None,0,false),
         new OpcodeInfo("ldloc.1",Opcode.LDLOC_1,OperandFormat.None,0,false),
         new OpcodeInfo("ldloc.2",Opcode.LDLOC_2,OperandFormat.None,0,false),
         new OpcodeInfo("ldloc.3",Opcode.LDLOC_3,OperandFormat.None,0,false),
         new OpcodeInfo("stloc.0",Opcode.STLOC_0,OperandFormat.None,0,false),
         new OpcodeInfo("stloc.1",Opcode.STLOC_1,OperandFormat.None,0,false),
         new OpcodeInfo("stloc.2",Opcode.STLOC_2,OperandFormat.None,0,false),
         new OpcodeInfo("stloc.3",Opcode.STLOC_3,OperandFormat.None,0,false),
         new OpcodeInfo("ldarg.s",Opcode.LDARG_S,OperandFormat.ShortVar,1,false),
         new OpcodeInfo("ldarga.s",Opcode.LDARGA_S,OperandFormat.ShortVar,1,false),
         new OpcodeInfo("starg.s",Opcode.STARG_S,OperandFormat.ShortVar,1,false),
         new OpcodeInfo("ldloc.s",Opcode.LDLOC_S,OperandFormat.ShortVar,1,false),
         new OpcodeInfo("ldloca.s",Opcode.LDLOCA_S,OperandFormat.ShortVar,1,false),
         new OpcodeInfo("stloc.s",Opcode.STLOC_S,OperandFormat.ShortVar,1,false),
         new OpcodeInfo("ldnull",Opcode.LDNULL,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.m1",Opcode.LDC_I4_M1,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.0",Opcode.LDC_I4_0,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.1",Opcode.LDC_I4_1,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.2",Opcode.LDC_I4_2,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.3",Opcode.LDC_I4_3,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.4",Opcode.LDC_I4_4,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.5",Opcode.LDC_I4_5,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.6",Opcode.LDC_I4_6,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.7",Opcode.LDC_I4_7,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.8",Opcode.LDC_I4_8,OperandFormat.None,0,false),
         new OpcodeInfo("ldc.i4.s",Opcode.LDC_I4_S,OperandFormat.ShortInt,1,false),
         new OpcodeInfo("ldc.i4",Opcode.LDC_I4,OperandFormat.Int,4,false),
         new OpcodeInfo("ldc.i8",Opcode.LDC_I8,OperandFormat.Int8,8,false),
         new OpcodeInfo("ldc.r4",Opcode.LDC_R4,OperandFormat.ShortFloat,4,false),
         new OpcodeInfo("ldc.r8",Opcode.LDC_R8,OperandFormat.Float,8,false),
         new OpcodeInfo("unused",Opcode.UNUSED49,OperandFormat.Illegal,0,false),
         new OpcodeInfo("dup",Opcode.DUP,OperandFormat.None,0,false),
         new OpcodeInfo("pop",Opcode.POP,OperandFormat.None,0,false),
         new OpcodeInfo("jmp",Opcode.JMP,OperandFormat.Method,4,true),
         new OpcodeInfo("call",Opcode.CALL,OperandFormat.Method,4,false),
         new OpcodeInfo("calli",Opcode.CALLI,OperandFormat.Sig,4,false),
         new OpcodeInfo("ret",Opcode.RET,OperandFormat.None,0,true),
         new OpcodeInfo("br.s",Opcode.BR_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("brfalse.s",Opcode.BRFALSE_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("brtrue.s",Opcode.BRTRUE_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("beq.s",Opcode.BEQ_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("bge.s",Opcode.BGE_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("bgt.s",Opcode.BGT_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("ble.s",Opcode.BLE_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("blt.s",Opcode.BLT_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("bne.un.s",Opcode.BNE_UN_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("bge.un.s",Opcode.BGE_UN_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("bgt.un.s",Opcode.BGT_UN_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("ble.un.s",Opcode.BLE_UN_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("blt.un.s",Opcode.BLT_UN_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("br",Opcode.BR,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("brfalse",Opcode.BRFALSE,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("brtrue",Opcode.BRTRUE,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("beq",Opcode.BEQ,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("bge",Opcode.BGE,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("bgt",Opcode.BGT,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("ble",Opcode.BLE,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("blt",Opcode.BLT,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("bne.un",Opcode.BNE_UN,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("bge.un",Opcode.BGE_UN,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("bgt.un",Opcode.BGT_UN,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("ble.un",Opcode.BLE_UN,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("blt.un",Opcode.BLT_UN,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("switch",Opcode.SWITCH,OperandFormat.Switch,0xFF,true),
         new OpcodeInfo("ldind.i1",Opcode.LDIND_I1,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.u1",Opcode.LDIND_U1,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.i2",Opcode.LDIND_I2,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.u2",Opcode.LDIND_U2,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.i4",Opcode.LDIND_I4,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.u4",Opcode.LDIND_U4,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.i8",Opcode.LDIND_I8,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.i",Opcode.LDIND_I,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.r4",Opcode.LDIND_R4,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.r8",Opcode.LDIND_R8,OperandFormat.None,0,false),
         new OpcodeInfo("ldind.ref",Opcode.LDIND_REF,OperandFormat.None,0,false),
         new OpcodeInfo("stind.ref",Opcode.STIND_REF,OperandFormat.None,0,false),
         new OpcodeInfo("stind.i1",Opcode.STIND_I1,OperandFormat.None,0,false),
         new OpcodeInfo("stind.i2",Opcode.STIND_I2,OperandFormat.None,0,false),
         new OpcodeInfo("stind.i4",Opcode.STIND_I4,OperandFormat.None,0,false),
         new OpcodeInfo("stind.i8",Opcode.STIND_I8,OperandFormat.None,0,false),
         new OpcodeInfo("stind.r4",Opcode.STIND_R4,OperandFormat.None,0,false),
         new OpcodeInfo("stind.r8",Opcode.STIND_R8,OperandFormat.None,0,false),
         new OpcodeInfo("add",Opcode.ADD,OperandFormat.None,0,false),
         new OpcodeInfo("sub",Opcode.SUB,OperandFormat.None,0,false),
         new OpcodeInfo("mul",Opcode.MUL,OperandFormat.None,0,false),
         new OpcodeInfo("div",Opcode.DIV,OperandFormat.None,0,false),
         new OpcodeInfo("div.un",Opcode.DIV_UN,OperandFormat.None,0,false),
         new OpcodeInfo("rem",Opcode.REM,OperandFormat.None,0,false),
         new OpcodeInfo("rem.un",Opcode.REM_UN,OperandFormat.None,0,false),
         new OpcodeInfo("and",Opcode.AND,OperandFormat.None,0,false),
         new OpcodeInfo("or",Opcode.OR,OperandFormat.None,0,false),
         new OpcodeInfo("xor",Opcode.XOR,OperandFormat.None,0,false),
         new OpcodeInfo("shl",Opcode.SHL,OperandFormat.None,0,false),
         new OpcodeInfo("shr",Opcode.SHR,OperandFormat.None,0,false),
         new OpcodeInfo("shr.un",Opcode.SHR_UN,OperandFormat.None,0,false),
         new OpcodeInfo("neg",Opcode.NEG,OperandFormat.None,0,false),
         new OpcodeInfo("not",Opcode.NOT,OperandFormat.None,0,false),
         new OpcodeInfo("conv.i1",Opcode.CONV_I1,OperandFormat.None,0,false),
         new OpcodeInfo("conv.i2",Opcode.CONV_I2,OperandFormat.None,0,false),
         new OpcodeInfo("conv.i4",Opcode.CONV_I4,OperandFormat.None,0,false),
         new OpcodeInfo("conv.i8",Opcode.CONV_I8,OperandFormat.None,0,false),
         new OpcodeInfo("conv.r4",Opcode.CONV_R4,OperandFormat.None,0,false),
         new OpcodeInfo("conv.r8",Opcode.CONV_R8,OperandFormat.None,0,false),
         new OpcodeInfo("conv.u4",Opcode.CONV_U4,OperandFormat.None,0,false),
         new OpcodeInfo("conv.u8",Opcode.CONV_U8,OperandFormat.None,0,false),
         new OpcodeInfo("callvirt",Opcode.CALLVIRT,OperandFormat.Method,4,false),
         new OpcodeInfo("cpobj",Opcode.CPOBJ,OperandFormat.Type,4,false),
         new OpcodeInfo("ldobj",Opcode.LDOBJ,OperandFormat.Type,4,false),
         new OpcodeInfo("ldstr",Opcode.LDSTR,OperandFormat.String,4,false),
         new OpcodeInfo("newobj",Opcode.NEWOBJ,OperandFormat.Method,4,false),
         new OpcodeInfo("castclass",Opcode.CASTCLASS,OperandFormat.Type,4,false),
         new OpcodeInfo("isinst",Opcode.ISINST,OperandFormat.Type,4,false),
         new OpcodeInfo("conv.r.un",Opcode.CONV_R_UN,OperandFormat.None,0,false),
         new OpcodeInfo("ann.data.s",Opcode.ANN_DATA_S,OperandFormat.ShortBranchTarget,0xFF,false),
         new OpcodeInfo("unused",Opcode.UNUSED1,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unbox",Opcode.UNBOX,OperandFormat.Type,4,false),
         new OpcodeInfo("throw",Opcode.THROW,OperandFormat.None,0,true),
         new OpcodeInfo("ldfld",Opcode.LDFLD,OperandFormat.Field,4,false),
         new OpcodeInfo("ldflda",Opcode.LDFLDA,OperandFormat.Field,4,false),
         new OpcodeInfo("stfld",Opcode.STFLD,OperandFormat.Field,4,false),
         new OpcodeInfo("ldsfld",Opcode.LDSFLD,OperandFormat.Field,4,false),
         new OpcodeInfo("ldsflda",Opcode.LDSFLDA,OperandFormat.Field,4,false),
         new OpcodeInfo("stsfld",Opcode.STSFLD,OperandFormat.Field,4,false),
         new OpcodeInfo("stobj",Opcode.STOBJ,OperandFormat.Type,4,false),
         new OpcodeInfo("conv.ovf.i1.un",Opcode.CONV_OVF_I1_UN,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.i2.un",Opcode.CONV_OVF_I2_UN,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.i4.un",Opcode.CONV_OVF_I4_UN,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.i8.un",Opcode.CONV_OVF_I8_UN,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u1.un",Opcode.CONV_OVF_U1_UN,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u2.un",Opcode.CONV_OVF_U2_UN,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u4.un",Opcode.CONV_OVF_U4_UN,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u8.un",Opcode.CONV_OVF_U8_UN,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.i.un",Opcode.CONV_OVF_I_UN,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u.un",Opcode.CONV_OVF_U_UN,OperandFormat.None,0,false),
         new OpcodeInfo("box",Opcode.BOX,OperandFormat.Type,4,false),
         new OpcodeInfo("newarr",Opcode.NEWARR,OperandFormat.Type,4,false),
         new OpcodeInfo("ldlen",Opcode.LDLEN,OperandFormat.None,0,false),
         new OpcodeInfo("ldelema",Opcode.LDELEMA,OperandFormat.Type,4,false),
         new OpcodeInfo("ldelem.i1",Opcode.LDELEM_I1,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.u1",Opcode.LDELEM_U1,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.i2",Opcode.LDELEM_I2,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.u2",Opcode.LDELEM_U2,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.i4",Opcode.LDELEM_I4,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.u4",Opcode.LDELEM_U4,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.i8",Opcode.LDELEM_I8,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.i",Opcode.LDELEM_I,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.r4",Opcode.LDELEM_R4,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.r8",Opcode.LDELEM_R8,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem.ref",Opcode.LDELEM_REF,OperandFormat.None,0,false),
         new OpcodeInfo("stelem.i",Opcode.STELEM_I,OperandFormat.None,0,false),
         new OpcodeInfo("stelem.i1",Opcode.STELEM_I1,OperandFormat.None,0,false),
         new OpcodeInfo("stelem.i2",Opcode.STELEM_I2,OperandFormat.None,0,false),
         new OpcodeInfo("stelem.i4",Opcode.STELEM_I4,OperandFormat.None,0,false),
         new OpcodeInfo("stelem.i8",Opcode.STELEM_I8,OperandFormat.None,0,false),
         new OpcodeInfo("stelem.r4",Opcode.STELEM_R4,OperandFormat.None,0,false),
         new OpcodeInfo("stelem.r8",Opcode.STELEM_R8,OperandFormat.None,0,false),
         new OpcodeInfo("stelem.ref",Opcode.STELEM_REF,OperandFormat.None,0,false),
         new OpcodeInfo("ldelem",Opcode.LDELEM,OperandFormat.Type,4,false),
         new OpcodeInfo("stelem",Opcode.STELEM,OperandFormat.Type,4,false),
         new OpcodeInfo("unbox.any",Opcode.UNBOX_ANY,OperandFormat.Type,4,false),
         new OpcodeInfo("unused",Opcode.UNUSED5,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED6,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED7,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED8,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED9,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED10,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED11,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED12,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED13,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED14,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED15,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED16,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED17,OperandFormat.Illegal,0,false),
         new OpcodeInfo("conv.ovf.i1",Opcode.CONV_OVF_I1,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u1",Opcode.CONV_OVF_U1,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.i2",Opcode.CONV_OVF_I2,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u2",Opcode.CONV_OVF_U2,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.i4",Opcode.CONV_OVF_I4,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u4",Opcode.CONV_OVF_U4,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.i8",Opcode.CONV_OVF_I8,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u8",Opcode.CONV_OVF_U8,OperandFormat.None,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED50,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED18,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED19,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED20,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED21,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED22,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED23,OperandFormat.Illegal,0,false),
         new OpcodeInfo("refanyval",Opcode.REFANYVAL,OperandFormat.Type,4,false),
         new OpcodeInfo("ckfinite",Opcode.CKFINITE,OperandFormat.None,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED24,OperandFormat.None,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED25,OperandFormat.None,0,false),
         new OpcodeInfo("mkrefany",Opcode.MKREFANY,OperandFormat.Type,4,false),
         new OpcodeInfo("ann.call",Opcode.ANN_CALL,OperandFormat.Method,4,false),
         new OpcodeInfo("ann.catch",Opcode.ANN_CATCH,OperandFormat.None,0,false),
         new OpcodeInfo("ann.dead",Opcode.ANN_DEAD,OperandFormat.Var,2,false),
         new OpcodeInfo("ann.hoisted",Opcode.ANN_HOISTED,OperandFormat.None,0,false),
         new OpcodeInfo("ann.hoisted_call",Opcode.ANN_HOISTED_CALL,OperandFormat.Method,4,false),
         new OpcodeInfo("ann.lab",Opcode.ANN_LAB,OperandFormat.None,0,false),
         new OpcodeInfo("ann.def",Opcode.ANN_DEF,OperandFormat.None,0,false),
         new OpcodeInfo("ann.ref.s",Opcode.ANN_REF_S,OperandFormat.ShortVar,1,false),
         new OpcodeInfo("ann.phi",Opcode.ANN_PHI,OperandFormat.InlinePhi,0xFF,false),
         new OpcodeInfo("ldtoken",Opcode.LDTOKEN,OperandFormat.Token,4,false),
         new OpcodeInfo("conv.u2",Opcode.CONV_U2,OperandFormat.None,0,false),
         new OpcodeInfo("conv.u1",Opcode.CONV_U1,OperandFormat.None,0,false),
         new OpcodeInfo("conv.i",Opcode.CONV_I,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.i",Opcode.CONV_OVF_I,OperandFormat.None,0,false),
         new OpcodeInfo("conv.ovf.u",Opcode.CONV_OVF_U,OperandFormat.None,0,false),
         new OpcodeInfo("add.ovf",Opcode.ADD_OVF,OperandFormat.None,0,false),
         new OpcodeInfo("add.ovf.un",Opcode.ADD_OVF_UN,OperandFormat.None,0,false),
         new OpcodeInfo("mul.ovf",Opcode.MUL_OVF,OperandFormat.None,0,false),
         new OpcodeInfo("mul.ovf.un",Opcode.MUL_OVF_UN,OperandFormat.None,0,false),
         new OpcodeInfo("sub.ovf",Opcode.SUB_OVF,OperandFormat.None,0,false),
         new OpcodeInfo("sub.ovf.un",Opcode.SUB_OVF_UN,OperandFormat.None,0,false),
         new OpcodeInfo("endfinally",Opcode.ENDFINALLY,OperandFormat.None,0,true),
         new OpcodeInfo("leave",Opcode.LEAVE,OperandFormat.BranchTarget,4,true),
         new OpcodeInfo("leave.s",Opcode.LEAVE_S,OperandFormat.ShortBranchTarget,1,true),
         new OpcodeInfo("stind.i",Opcode.STIND_I,OperandFormat.None,0,false),
         new OpcodeInfo("conv.u",Opcode.CONV_U,OperandFormat.None,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED26,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED27,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED28,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED29,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED30,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED31,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED32,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED33,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED34,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED35,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED36,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED37,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED38,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED39,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED40,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED41,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED42,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED43,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED44,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED45,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED46,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED47,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED48,OperandFormat.Illegal,0,false),
         new OpcodeInfo("prefix7",Opcode.PREFIX7,OperandFormat.Illegal,0,false),
         new OpcodeInfo("prefix6",Opcode.PREFIX6,OperandFormat.Illegal,0,false),
         new OpcodeInfo("prefix5",Opcode.PREFIX5,OperandFormat.Illegal,0,false),
         new OpcodeInfo("prefix4",Opcode.PREFIX4,OperandFormat.Illegal,0,false),
         new OpcodeInfo("prefix3",Opcode.PREFIX3,OperandFormat.Illegal,0,false),
         new OpcodeInfo("prefix2",Opcode.PREFIX2,OperandFormat.Illegal,0,false),
         new OpcodeInfo("prefix1",Opcode.PREFIX1,OperandFormat.None,0,false),
         new OpcodeInfo("prefixref",Opcode.PREFIXREF,OperandFormat.Illegal,0,false),
         new OpcodeInfo("arglist",Opcode.ARGLIST,OperandFormat.None,0,false),
         new OpcodeInfo("ceq",Opcode.CEQ,OperandFormat.None,0,false),
         new OpcodeInfo("cgt",Opcode.CGT,OperandFormat.None,0,false),
         new OpcodeInfo("cgt.un",Opcode.CGT_UN,OperandFormat.None,0,false),
         new OpcodeInfo("clt",Opcode.CLT,OperandFormat.None,0,false),
         new OpcodeInfo("clt.un",Opcode.CLT_UN,OperandFormat.None,0,false),
         new OpcodeInfo("ldftn",Opcode.LDFTN,OperandFormat.Method,4,false),
         new OpcodeInfo("ldvirtftn",Opcode.LDVIRTFTN,OperandFormat.Method,4,false),
         new OpcodeInfo("unused",Opcode.UNUSED56,OperandFormat.Illegal,0,false),
         new OpcodeInfo("ldarg",Opcode.LDARG,OperandFormat.Var,2,false),
         new OpcodeInfo("ldarga",Opcode.LDARGA,OperandFormat.Var,2,false),
         new OpcodeInfo("starg",Opcode.STARG,OperandFormat.Var,2,false),
         new OpcodeInfo("ldloc",Opcode.LDLOC,OperandFormat.Var,2,false),
         new OpcodeInfo("ldloca",Opcode.LDLOCA,OperandFormat.Var,2,false),
         new OpcodeInfo("stloc",Opcode.STLOC,OperandFormat.Var,2,false),
         new OpcodeInfo("localloc",Opcode.LOCALLOC,OperandFormat.None,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED57,OperandFormat.Illegal,0,false),
         new OpcodeInfo("endfilter",Opcode.ENDFILTER,OperandFormat.None,0,true),
         new OpcodeInfo("unaligned.",Opcode.UNALIGNED,OperandFormat.ShortInt,1,false),
         new OpcodeInfo("volatile.",Opcode.VOLATILE,OperandFormat.None,0,false),
         new OpcodeInfo("tail.",Opcode.TAILCALL,OperandFormat.None,0,false),
         new OpcodeInfo("initobj",Opcode.INITOBJ,OperandFormat.Type,4,false),
         new OpcodeInfo("ann.live",Opcode.ANN_LIVE,OperandFormat.Var,2,false),
         new OpcodeInfo("cpblk",Opcode.CPBLK,OperandFormat.None,0,false),
         new OpcodeInfo("initblk",Opcode.INITBLK,OperandFormat.None,0,false),
         new OpcodeInfo("ann.ref",Opcode.ANN_REF,OperandFormat.Var,2,false),
         new OpcodeInfo("rethrow",Opcode.RETHROW,OperandFormat.None,0,true),
         new OpcodeInfo("unused",Opcode.UNUSED51,OperandFormat.Illegal,0,false),
         new OpcodeInfo("sizeof",Opcode.SIZEOF,OperandFormat.Type,4,false),
         new OpcodeInfo("refanytype",Opcode.REFANYTYPE,OperandFormat.None,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED52,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED53,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED54,OperandFormat.Illegal,0,false),
         new OpcodeInfo("unused",Opcode.UNUSED55,OperandFormat.Illegal,0,false),
         new OpcodeInfo("ann.data",Opcode.ANN_DATA,OperandFormat.BranchTarget,0xFF,false),
         new OpcodeInfo("illegal",Opcode.ILLEGAL,OperandFormat.Illegal,0,false),
         new OpcodeInfo("endmac",Opcode.MACRO_END,OperandFormat.Illegal,0,false),
      };

      static Instruction() {
          for (Opcode opcode = 0; opcode < Opcode.COUNT; opcode++) {
              if (opcodeInfoTable[(int) opcode].opcode != opcode) {
                  throw new IllegalInstructionStreamException("opcode invariant failure");
              }
          }
      }

      // Internal classes

      public abstract class Operand {
      }

      public class OperandInt: Operand {

          // Constructor Methods

          internal OperandInt(int value) {
              this.value = value;
          }

          // Access Methods
          public int Value {
              get {
                  return this.value;
              }
          }

          // Debug Methods

          public override String ToString() {
              return ("OperandInt(0x"+this.value.ToString("x")+"/"+this.value+")");
          }

          // State

          private readonly int value;

      }

      public class OperandTarget: Operand {

          // Constructor Methods

          internal OperandTarget(int target) {
              this.target = target;
          }

          // Access Methods

          public int Target {
              get {
                  return this.target;
              }
          }

          // Debug Methods

          public override String ToString() {
              return ("OperandTarget(IL_"+this.target.ToString("x4")+")");
          }

          // State

          private readonly int target;

      }

      public class OperandSingle: Operand {

          // Constructor Methods

          internal OperandSingle(float value) {
              this.value = value;
          }

          // Access Methods

          public float Value {
              get {
                  return this.value;
              }
          }

          // Debug Methods

          public override String ToString() {
              return ("OperandSingle("+this.value+")");
          }

          // State

          private readonly float value;

      }

      public class OperandDouble: Operand {

          // Constructor Methods

          internal OperandDouble(double value) {
              this.value = value;
          }

          // Access Methods

          public double Value {
              get {
                  return this.value;
              }
          }

          // Debug Methods

          public override String ToString() {
              return ("OperandDouble("+this.value+")");
          }

          // State

          private readonly double value;

      }

      public class OperandTargetArray: Operand {

          // Constructor Methods

          internal OperandTargetArray(int[] targets) {
              this.targets = targets;
          }

          // Access Methods

          public int[] Targets {
              get {
                  return this.targets;
              }
          }

          // Debug Methods

          public override String ToString() {
              System.Text.StringBuilder sb =
                  new System.Text.StringBuilder("OperandTargetArray(");
              if (this.targets.Length > 0) {
                  for (int i = 0; i < this.targets.Length - 1; i++) {
                      sb.Append("IL_");
                      sb.Append(this.targets[i].ToString("x4"));
                      sb.Append(",");
                  }
                  sb.Append("IL_");
                  sb.Append(this.targets[this.targets.Length-1].ToString("x4"));
              }
              sb.Append(")");
              return sb.ToString();
          }

          // State

          private readonly int[] targets;

      }

      public class OperandByteArray: Operand {

          // Constructor Methods

          internal OperandByteArray(byte[] value) {
              this.value = value;
          }

          // Access Methods

          public byte[] Value {
              get {
                  return this.value;
              }
          }

          // Debug Methods

          public override String ToString() {
              System.Text.StringBuilder sb =
                  new System.Text.StringBuilder("OperandByteArray(");
              if (this.value.Length > 0) {
                  for (int i = 0; i < this.value.Length - 1; i++) {
                      sb.Append(this.value[i]);
                      sb.Append(",");
                  }
                  sb.Append(this.value[this.value.Length-1]);
              }
              sb.Append(")");
              return sb.ToString();
          }

          // State

          private readonly byte[] value;

      }

      public class OperandLong: Operand {

          // Constructor Methods

          internal OperandLong(long value) {
              this.value = value;
          }

          // Access Methods

          public long Value {
              get {
                  return this.value;
              }
          }

          // Debug Methods

          public override String ToString() {
              return ("OperandLong("+this.value+")");
          }

          // State

          private readonly long value;

      }

      public class OperandString: Operand {

          // Constructor Methods

          internal OperandString(String value) {
              this.value = value;
          }

          // Access Methods

          public String Value {
              get {
                  return this.value;
              }
          }

          // Debug Methods

          public override String ToString() {
              return ("OperandString(\""+this.value+"\")");
          }

          // State

          private readonly String value;

      }

      public class OperandObject: Operand {

          // Constructor Methods

          internal OperandObject(MetaDataObject value) {
              this.value = value;
          }

          // Access Methods

          public MetaDataObject Value {
              get {
                  return this.value;
              }
          }

          // Debug Methods

          public override String ToString() {
              return ("OperandObject("+this.value+")");
          }

          // State

          private readonly MetaDataObject value;

      }

      private class OpcodeInfo {

          // Constructor Methods

          internal OpcodeInfo(String name, Opcode opcode,
                              OperandFormat operandFormat, byte operandSize,
                              bool isControl) {
              this.name = name;
              this.opcode = opcode;
              this.operandFormat = operandFormat;
              this.operandSize = operandSize;
              this.isControl = isControl;
          }

          // State

          internal readonly String name;
          internal readonly Opcode opcode;
          internal readonly OperandFormat operandFormat;
          internal readonly byte operandSize;
          internal readonly bool isControl;

      }

      private class IllegalInstructionStreamException: Exception {

          internal IllegalInstructionStreamException(String message):
              base(message)
          { }

      }

  }

}
