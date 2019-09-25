// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataEvent: MetaDataObject {

      // Constructor Methods

      internal MetaDataEvent(short flags, String name, int eventTypeIndex) {
          this.flags = (EventAttributes) flags;
          this.name = name;
          this.eventTypeIndex = eventTypeIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.eventType = loader.getTypeDefOrRef(this.eventTypeIndex);
      }

      // Access Methods

      public EventAttributes Flags {
          get {
              return this.flags;
          }
      }

      public String Name {
          get {
              return this.name;
          }
      }

      // Returns one of MetaData{TypeDef,TypeRef,TypeSpec}
      public MetaDataObject Type {
          get {
              return this.eventType;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.eventType == null) {
              return ("MetaDataEvent("+this.flags+","+this.name+","+
                      this.eventTypeIndex+")");
          }
          else {
              return ("MetaDataEvent("+this.flags+","+this.name+","+
                      this.eventType+")");
          }
      }

      // State

      private readonly EventAttributes flags;
      private readonly String          name;
      private readonly int             eventTypeIndex;
      private          MetaDataObject  eventType;

      // Internal classes

      // Section 22.1.2 of ECMA spec, Section II
      public enum EventAttributes {
          SpecialName               =   0x0200, // event is special.  Name describes how.
              // Reserved flags for Runtime use only.
              ReservedMask          =   0x0400,
              RTSpecialName         =   0x0400 // Runtime(metadata internal APIs) should check name encoding.
      }

  }

}
