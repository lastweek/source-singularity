//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//
 
namespace Bartok.DebugInfo
{
  using System;
  using System.Text;
  public abstract class DebugLineNumber {
      public int LineNumber {
          get { return lineNumber; }
      }

      public String SrcFileName {
          get { return srcFileName; }
      }

      protected int lineNumber;
      protected String srcFileName; 
  }

  public class CoffLineNumber : DebugLineNumber {
      public CoffLineNumber(int lineNumber, String srcFileName) {
          this.lineNumber = lineNumber;
          this.srcFileName = srcFileName;
      }
      
      public override String ToString() {
          StringBuilder s = new StringBuilder();
          s.Append("      ;#");
          s.Append(lineNumber);
          s.Append("      ");
          s.Append(srcFileName);
          return s.ToString();
      }
  }

  public class CVLineNumber : DebugLineNumber {
      public CVLineNumber(int lineNumber, int column, String srcFileName) {
          this.lineNumber = lineNumber;
          this.column = column;
          this.srcFileName = srcFileName;
      }

      public int Column {
          get { return column; }
      }

      public override String ToString() {
          StringBuilder s = new StringBuilder();
          s.Append("      ;#");
          s.Append(lineNumber);
          s.Append("      ");
          s.Append(column);
          s.Append("      ");
          s.Append(srcFileName);
          return s.ToString();
      }

      private int column;
  }

}
