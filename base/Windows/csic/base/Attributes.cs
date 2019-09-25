using System;
using System.IO;

[AttributeUsage(AttributeTargets.Field|AttributeTargets.Property)]
public class MayBeNullAttribute: Attribute {}

[AttributeUsage(AttributeTargets.Assembly,AllowMultiple=true)]
public class SourceInfoAttribute: Attribute {
	public string Id = null;
	public SourceInfoAttribute(string Id) { this.Id = Id; }
}

[AttributeUsage(AttributeTargets.Field|AttributeTargets.Property)]
public class Bind1Attribute: Attribute {}
[AttributeUsage(AttributeTargets.Field|AttributeTargets.Property)]
public class Bind2Attribute: Attribute {}
[AttributeUsage(AttributeTargets.Field|AttributeTargets.Property)]
public class Bind3Attribute: Attribute {}
[AttributeUsage(AttributeTargets.Field|AttributeTargets.Property)]
public class TypecheckAttribute: Attribute {}
[AttributeUsage(AttributeTargets.Field|AttributeTargets.Property)]
public class ILGenAttribute: Attribute {}
[AttributeUsage(AttributeTargets.Field|AttributeTargets.Property)]
public class RewriteAttribute: Attribute {}
[AttributeUsage(AttributeTargets.Field|AttributeTargets.Property)]
public class EmitAttribute: Attribute {}

