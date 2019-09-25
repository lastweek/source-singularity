//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;

namespace Bartok.MSIL
{

  public class MetaDataMethodSemantics: MetaDataObject {

      // Constructor Methods

      internal MetaDataMethodSemantics(short semantic, int methodIndex,
                                       int associationIndex) {
          this.semantic = semantic;
          this.methodIndex = methodIndex;
          this.associationIndex = associationIndex;
      }

      // This is technically not a constructor method, but it is meant to
      // be used to set up the object
      internal void resolveReferences(MetaDataLoader loader) {
          this.method = loader.getMethod(this.methodIndex);
          this.association = loader.getHasSemantic(this.associationIndex);
      }

      // Access Methods

      // Bitmask described by MethodSemanticsAttribute
      public short Semantic {
          get {
              return this.semantic;
          }
      }

      public MetaDataMethod Method {
          get {
              return this.method;
          }
      }

      public MetaDataObject Association {
          get {
              return this.association;
          }
      }

      // Debug Methods

      public override String ToString() {
          if (this.method == null || this.association == null) {
              return ("MetaDataMethodSemantics("+this.semantic+","+
                      this.methodIndex+","+this.associationIndex+")");
          }
          else {
              return ("MetaDataMethodSemantics("+this.semantic+","+
                      this.method+","+this.association+")");
          }
      }

      // State

      private readonly short          semantic;
      private readonly int            methodIndex;
      private          MetaDataMethod method;
      private readonly int            associationIndex;
      private          MetaDataObject association;

      // Internal Classes

      // Section 22.1.8 of ECMA spec, Section II
      public enum MethodSemanticsAttributes {
          Setter       = 0x0001, // Setter for property
              Getter   = 0x0002, // Getter for property
              Other    = 0x0004, // other method for property or event
              AddOn    = 0x0008, // AddOn method for event
              RemoveOn = 0x0010, // RemoveOn method for event
              Fire     = 0x0020  // Fire method for event
      }

  }

}
