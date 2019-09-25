// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataBlob {

      // Constructor Methods

      internal MetaDataBlob(byte[] buffer) {
          this.buffer = buffer;
      }

      // Debug Methods

      public override String ToString() {
          System.Text.StringBuilder sb =
              new System.Text.StringBuilder("MetaDataBlob(");
          int bufferSize = buffer.Length;
          if (bufferSize > 0) {
              sb.Append(buffer[0].ToString("x2"));
              for (int i = 1; i < bufferSize; i++) {
                  sb.Append(",");
                  sb.Append(buffer[i].ToString("x2"));
              }
          }
          sb.Append(")");
          return sb.ToString();
      }

      // State

      private readonly byte[] buffer;

  }

}
