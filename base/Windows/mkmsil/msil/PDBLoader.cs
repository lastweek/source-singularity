//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{
  using System.Runtime.InteropServices;
  using System.Runtime.CompilerServices;
  using System.Text;

  public sealed class PDBLoader {
      public static int OpenPdbFile(string srcName)
      {
          return -1;
      }


      public static int ClosePdbFile()
      {
          return -1;
      }


      public static void GetLineNumberCount(
                int token,
                out long count,
                out uint length)
      {
          count = 0;
          length = 0;
      }

      public static int LoadLineNumber(
                int token,
                [In, Out] int[] lines,
                [In, Out] int[] columns,
                [In, Out] int[] offsets,
                StringBuilder fileName)
      {
          return -1;
      }


      public static int GetMethodCount(
                out int varCount,
                out int nameLength)
      {
          varCount = 0;
          nameLength = 0;

          return -1;
      }

      public static int GetNextVar(
                out int slot,
                out int token,
                StringBuilder varName)
      {
          slot = 0;
          token = 0;

          return -1;
      }


      public static int OpenSymbolTable()
      {
          return -1;
      }

      public static int CloseSymbolTable()
      {
          return -1;
      }

      public static int NextSymbolTable()
      {
          return -1;
      }
  }
}
