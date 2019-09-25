using System;

namespace Microsoft.SingSharp.Reflection{
	public class AttributePatternAttribute : Attribute {
		Object type;
		public Object Type {
			get { return type; }
			set { type = value; }
		}

		object[] expressions;
		public object[] Expressions{
			get { return expressions; }
			set { expressions = value; }
		}
	}

	public class ForAllStatementIndex : Attribute {
		public ForAllStatementIndex(int index) {}
	}

	public class ForAllSummaryAttribute : Attribute {
		public ForAllSummaryAttribute(string summary){}
	}
	
	public class ReflectionAttribute : Attribute {
        public enum Type {
            None,
            Index,
            IndexMap,
            Generate,
            Implement,
            Container,
            NodeMap,
            Pattern,
            Subtype,
            Shadow,
            Reflective,
            ExpressionBinding,
            Scope,
        }
		public ReflectionAttribute(Type type){}
		
		uint flags;
		public uint Flags {
			get {return flags; }
			set {flags = value; }
		}
		
	}

	#region parameter attributes
	[AttributeUsage(AttributeTargets.Parameter)]
	public class ParameterPatternAttribute : Attribute {
		string type;
		public string Type{
			get {return type; }
			set {type = value; }
		}
		bool typeIsVariable;
		public bool TypeIsVariable {
			get {return typeIsVariable; }
			set {typeIsVariable = value; }
		}	
	}

	[AttributeUsage(AttributeTargets.Parameter)]
	public class StarParameterPatternAttribute : ParameterPatternAttribute {}
	#endregion

	[AttributeUsage(AttributeTargets.Module | AttributeTargets.Assembly,
                    AllowMultiple=true)]
	public class TransformAttribute : Attribute {
		public Type Transform;
		public TransformAttribute(Type transformToRun) {
			this.Transform = transformToRun;
		}

		string[] namespaces;
		public string[] Namespaces {
			get { return namespaces; }
			set { namespaces = value; }
		}
		string [] files;
		public string[] Files {
			get { return files; }
			set { files = value; }
		}

		Type[] types;
		public Type[] Types {
			get  { return types; }
			set { types = Types; }
		}
	}
	
}

#if CCINamespace
namespace Microsoft.Cci.TypeExtensions {
#else
namespace System.Compiler.TypeExtensions {
#endif
	public interface IReflectionTransform {}
  public interface IReflectionScopePattern { }
  public interface IReflectionContainer {}
  public interface IReflectionTypeVariable {}
}
