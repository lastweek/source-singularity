// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataEventMap: MetaDataObject {

      // Constructor Methods

      internal MetaDataEventMap(int parentIndex, int eventListIndex) {
          this.parentIndex = parentIndex;
          this.eventListIndex = eventListIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.parent = loader.getTypeDef(this.parentIndex);
          this.eventObject = loader.getEvent(this.eventListIndex);
      }

      // Access Methods

      public MetaDataTypeDefinition Parent {
          get {
              return this.parent;
          }
      }

      public MetaDataEvent Event {
          get {
              return this.eventObject;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (parent == null || eventObject == null) {
              return ("MetaDataEventMap("+this.parentIndex+","+
                      this.eventListIndex+")");
          }
          else {
              return ("MetaDataEventMap("+this.parent+","+
                      this.eventObject+")");
          }
      }

      // State

      private readonly int                    parentIndex;
      private          MetaDataTypeDefinition parent;
      private readonly int                    eventListIndex;
      private          MetaDataEvent          eventObject;

  }

}
