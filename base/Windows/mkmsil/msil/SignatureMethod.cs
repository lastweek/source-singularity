// 
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.Text;

namespace Bartok.MSIL
{

  public class SignatureMethod: Signature {

      // Constructor Methods

      internal SignatureMethod(CallingConventions callingConvention,
                               uint genericParameterCount,
                               Type returnType,
                               Param[] parameters,
                               int sentinelLocation) {
          this.callingConvention = callingConvention;
          this.genericParameterCount = genericParameterCount;
          this.returnType = returnType;
          this.parameters = parameters;
          this.sentinelLocation = sentinelLocation;
      }

      // Access Methods

      public CallingConventions CallingConvention {
          get { return callingConvention; }
      }

      public uint GenericParameterCount {
          get { return genericParameterCount; }
      }

      public Type ReturnType {
          get { return returnType; }
      }
      
      public Param[] Parameters {
          get { return parameters; }
      }

      public int SentinelLocation {
          get { return sentinelLocation; }
      }

      // other handy methods
      
      public bool HasThis {
          get { return ((((int)callingConvention) &
                         ((int)Signature.CallingConventions.HasThis)) != 0);
          }
      }

      public bool ExplicitThis {
          get { return ((((int)callingConvention) &
                         ((int)Signature.CallingConventions.ExplicitThis)) != 0);
          }
      }

      public bool NoThis {
          get { return !(HasThis || ExplicitThis); }
      }

      // Debug Methods

      public override String ToString() {
          StringBuilder sb = new StringBuilder("SignatureMethod(");
          sb.Append(((uint) callingConvention).ToString("x"));
          sb.Append(",");
          sb.Append(genericParameterCount);
          sb.Append(",");
          sb.Append(returnType);
          sb.Append(",");
          sb.Append("parameters(");
          if (parameters.Length > 0) {
              sb.Append(parameters[0]);
              for (int i = 1; i < parameters.Length; i++) {
                  sb.Append(",");
                  sb.Append(parameters[i]);
              }
          }
          sb.Append("),");
          sb.Append(sentinelLocation);
          sb.Append(")");
          return sb.ToString();
      }

      // State

      private readonly CallingConventions callingConvention;
      private readonly uint               genericParameterCount;
      private readonly Type               returnType;
      private readonly Param[]            parameters;
      private readonly int                sentinelLocation;

  }

}
