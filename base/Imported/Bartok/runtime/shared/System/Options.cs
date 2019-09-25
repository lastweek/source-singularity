//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


namespace Microsoft.Bartok.Options {

  using System;

  [AttributeUsage(AttributeTargets.Class|
                  AttributeTargets.Struct|
                  AttributeTargets.Enum)]
  public sealed class MixinAttribute : Attribute {
      internal Type option;
      public MixinAttribute(Type type) {
          this.option = type;
      }
  }

  [AttributeUsage(AttributeTargets.Class|
                  AttributeTargets.Struct|
                  AttributeTargets.Enum,
                  AllowMultiple=true)]
  public sealed class MixinConditionalAttribute : Attribute {
      internal String option;
      public MixinConditionalAttribute(String option) {
          this.option = option;
      }
  }

  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Constructor|
                  AttributeTargets.Field)]
  public sealed class MixinOverrideAttribute : Attribute {
  }

  [AttributeUsage(AttributeTargets.Method|
                  AttributeTargets.Constructor)]
  public sealed class MixinExtendAttribute : Attribute {
      internal String option;
      public MixinExtendAttribute(String option) {
          this.option = option;
      }
  }

}
