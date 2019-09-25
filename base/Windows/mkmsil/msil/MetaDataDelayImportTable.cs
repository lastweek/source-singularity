//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

namespace Bartok.MSIL
{

  using System;
  using System.Text;

  public class MetaDataDelayImportTable: MetaDataObject {
      // Constructor Methods
      internal MetaDataDelayImportTable(string dllName, object[] importTable,
                                        string[] importNames) {
          this.dllName = dllName;
          int count = importTable.Length;
          this.imports = new int[count];
          for (int i = 0; i < count; i++) {
              this.imports[i] = (int) importTable[i];
          }
          this.names = importNames;
      }

      // Access Methods
      public String DllName {
          get { return this.dllName; }
      }

      public int[] Imports {
          get { return this.imports; }
      }

      public String[] Names {
          get { return this.names; }
      }

      public override string ToString() {
          StringBuilder sb = new StringBuilder("MetaDataDelayImportTable(");
          sb.Append(this.dllName + ")");
          for (int i = 0; i < imports.Length; i++) {
              sb.Append("<" + imports[i] + ">" + " " + names[i] + " ");
          }
          return sb.ToString();
      }

      //
      private readonly String dllName;
      private readonly int[] imports;
      private readonly String[] names;
  }
}
