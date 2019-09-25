// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class EHClause {

      // Constructor Methods

      internal EHClause(int flags, int tryOffset, int tryLength,
                        int handlerOffset, int handlerLength,
                        int filterOffset, MetaDataObject classObject) {
          this.flags = (ExceptionFlag) flags;
          this.tryOffset = tryOffset;
          this.tryEnd = tryOffset + tryLength;
          this.handlerOffset = handlerOffset;
          this.handlerEnd = handlerOffset + handlerLength;
          this.filterOffset = filterOffset;
          this.classObject = classObject;
      }

      // Access Methods

      public ExceptionFlag Flags {
          get {
              return this.flags;
          }
      }

      public int TryOffset {
          get {
              return this.tryOffset;
          }
      }

      public int TryEnd {
          get {
              return this.tryEnd;
          }
      }

      public int HandlerOffset {
          get {
              return this.handlerOffset;
          }
      }

      public int HandlerEnd {
          get {
              return this.handlerEnd;
          }
      }

      public int FilterOffset {
          get {
              return this.filterOffset;
          }
      }

      public MetaDataObject TypeObject {
          get {
              return this.classObject;
          }
      }

      // Debug Methods

      public override String ToString() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("EHClause(");
          sb.Append(this.flags);
          sb.Append(",try(");
          sb.Append(this.tryOffset.ToString("x"));
          sb.Append(",");
          sb.Append(this.tryEnd.ToString("x"));
          sb.Append("),handler(");
          sb.Append(this.handlerOffset.ToString("x"));
          sb.Append(",");
          sb.Append(this.handlerEnd.ToString("x"));
          sb.Append("),");
          sb.Append(this.filterOffset.ToString("x"));
          sb.Append(",");
          sb.Append(this.classObject);
          sb.Append(")");
          return sb.ToString();
      }

      internal static void dumpToConsole(EHClause[] ehClauses) {
          int count = ehClauses.Length;
          for (int i = 0; i < count; i++) {
              Console.WriteLine(ehClauses[i].ToString());
          }
      }

      // State

      private readonly ExceptionFlag  flags;
      private readonly int            tryOffset;
      private readonly int            tryEnd;
      private readonly int            handlerOffset;
      private readonly int            handlerEnd;
      private readonly int            filterOffset;
      private readonly MetaDataObject classObject;

      // Internal Classes

      public enum ExceptionFlag {
          None         = 0x0000,
              Filter   = 0x0001,
              Finally  = 0x0002,
              Fault    = 0x0004
      }

  }

}

