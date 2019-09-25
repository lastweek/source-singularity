// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataModule: MetaDataObject {

      // Constructor Methods

      internal MetaDataModule(short generation, String name,
                              int mvid, int encodingIndex,
                              Guid encoding, int encodingBaseIdIndex,
                              Guid encodingBaseId) {
          this.generation = generation;
          this.name = name;
          this.mvid = mvid;
          this.encodingIndex = encodingIndex;
          this.encoding = encoding;
          this.encodingBaseIdIndex = encodingBaseIdIndex;
          this.encodingBaseId = encodingBaseId;
      }

      // Access Methods

      public String Name {
          get {
              return this.name;
          }
      }

      public int MVID {
          get {
              return this.mvid;
          }
      }

      public Guid Encoding {
          get {
              return this.encoding;
          }
      }

      public Guid EncodingBaseId {
          get {
              return this.encodingBaseId;
          }
      }

      // Debug Methods

      public override String ToString() {
          return ("MetaDataModule("+this.name+","+this.mvid+","+
                  this.encoding+","+this.encodingBaseId+")");
      }

      public short Generation {
          get {
              return this.generation;
          }
      }

      // State

      private readonly short  generation;
      private readonly String name;
      private readonly int    mvid;
      private readonly int    encodingIndex;
      private          Guid   encoding;
      private readonly int    encodingBaseIdIndex;
      private          Guid   encodingBaseId;

  }

}
