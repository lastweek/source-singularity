// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataEventPtr: MetaDataObject {

      // Constructor Methods

      internal MetaDataEventPtr(int eventIndex) {
          this.eventIndex = eventIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.eventObject = loader.getEvent(this.eventIndex);
      }

      // Access Methods

      public MetaDataEvent Event {
          get {
              return this.eventObject;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.eventObject == null) {
              return ("MetaDataEventPtr("+this.eventIndex+")");
          }
          else {
              return ("MetaDataEventPtr("+this.eventObject+")");
          }
      }

      // State

      private readonly int           eventIndex;
      private          MetaDataEvent eventObject;

  }

}
