using System;
using System.Collections;
using System.CodeDom;

public class AST2CodeDom2 {

    private class Unsupported : Exception {
        public Unsupported(string s) : base(s) {
        }
    }

public static compilation visit(compilation ast, System.IO.TextWriter w, string[] args, MessageWriter msg) {
    if (msg.Count > 0)
        return ast;
    System.CodeDom.Compiler.CodeDomProvider cdp = new Microsoft.CSharp.CSharpCodeProvider();
    System.CodeDom.Compiler.ICodeGenerator icg = cdp.CreateGenerator();
    System.CodeDom.Compiler.CodeGeneratorOptions cgo = new System.CodeDom.Compiler.CodeGeneratorOptions();
    foreach (compilation_unit cu in ast.inputs) {
        CodeCompileUnit cd = emit_compilation_unit(cu);
        icg.GenerateCodeFromCompileUnit(cd, System.Console.Out, cgo);
    }
    return ast;
}

public static CodeCompileUnit Compile(compilation_unit cu) {
    return emit_compilation_unit(cu);
}

private static CodeTypeReference emit_name_type(name_type p) {
    string t0 = dotted2string(p.name);
    CodeTypeReference c = new CodeTypeReference(t0);
    c.UserData["AST"] = p;
    return c;
} // emit_name_type

private static CodeExpression emit_simple_name_expr(simple_name p) {
    return (CodeExpression) emit_simple_name(p);
}

private static bool isInsideAccessor(AST p) {
    for (AST a = p; a != null; a = a.parent) {
        if (a is accessor_declaration) {
            accessor_declaration ad = (accessor_declaration) a;
            if (ad.id.str == "set") {
                return true;
            }
        }
    }
    return false;
}

private static CodeObject emit_simple_name(simple_name p) {
    CodeObject o = null;
    CodeThisReferenceExpression self = null;
    if (p.sym.IsInstance) {
        self = new CodeThisReferenceExpression();
        self.UserData["AST"] = p;
    }
    if (p.sym is MethodSuite) {
        if (p.sym.IsInstance) {
            CodeMethodReferenceExpression mr = new CodeMethodReferenceExpression();
            mr.UserData["AST"] = p;
            mr.MethodName = p.id.str;
            mr.TargetObject = self;
            o = mr;
        } else {
            throw new Unsupported("unhandled sym type");
        }
    } else if (p.sym is Formal) {
        if (p.id.str == "value" && isInsideAccessor(p)) {
            CodePropertySetValueReferenceExpression psvre = new CodePropertySetValueReferenceExpression();
            psvre.UserData["AST"] = p;
            return psvre;
        }
        CodeArgumentReferenceExpression ar = new CodeArgumentReferenceExpression();
        ar.UserData["AST"] = p;
        ar.ParameterName = p.id.str;
        o = ar;
    } else if (p.sym is Local) {
        CodeVariableReferenceExpression lr = new CodeVariableReferenceExpression();
        lr.UserData["AST"] = p;
        lr.VariableName = p.id.str;
        o = lr;
    } else if (p.sym is Field) {
        if (p.sym.IsInstance) {
            CodeFieldReferenceExpression fr = new CodeFieldReferenceExpression();
            fr.UserData["AST"] = p;
            fr.FieldName = p.id.str;
            fr.TargetObject = self;
            o = fr;
        } else {
            throw new Unsupported("unhandled sym type");
        }
    } else if (p.sym is Property) {
        if (p.sym.IsInstance) {
            CodePropertyReferenceExpression pr = new CodePropertyReferenceExpression();
            pr.UserData["AST"] = p;
            pr.PropertyName = p.id.str;
            pr.TargetObject = self;
            o = pr;
        } else {
            throw new Unsupported("unhandled sym type");
        }
    } else if (p.sym is Event) {
        if (p.sym.IsInstance) {
            CodeEventReferenceExpression er = new CodeEventReferenceExpression();
            er.UserData["AST"] = p;
            er.EventName = p.id.str;
            er.TargetObject = self;
            o = er;
        } else {
            throw new Unsupported("unhandled sym type");
        }
    } else {
        throw new Unsupported("unhandled sym type: " + p.sym.ToString());
    }
    return o;
} // emit_simple_name

private static CodeStatement emit_expression_statement(expression_statement p) {
    if (p.expr is assignment_expression) {
        return emit_assignment_statement((assignment_expression)p.expr);
    }
    if (p.expr is compound_assignment_expression) {
        return emit_compound_assignment_statement((compound_assignment_expression)p.expr);
    }
    CodeExpressionStatement es = new CodeExpressionStatement();
    es.UserData["AST"] = es;
    CodeExpression t0 = emit_expression(p.expr);
    es.Expression = t0;
    return es;
} // emit_expression_statement

private static string get_member_name(member_name p) {
    string name = p.id.str;
    if (p.ty != null) {
        // WARNING: unimplemented interface names: member_name.ty
    }
    return name;
} // get_member_name

private static CodeCompileUnit emit_compilation(compilation p) {
    // WARNING: need to fix this
    foreach (compilation_unit x in p.inputs) {
        return emit_compilation_unit(x);
    }
    return null;
}

private static CodeAttributeDeclarationCollection emit_attribute_sections(attribute_sectionList attrs) {
    CodeAttributeDeclarationCollection adc = new CodeAttributeDeclarationCollection();
    foreach (attribute_section attr_section in attrs) {
        emit_attribute_section(attr_section, adc);
    }
    return adc;
}

private static void emit_attribute_section(attribute_section p, CodeAttributeDeclarationCollection cadc) {
    foreach (attribute attr in p.attributes) {
        CodeAttributeDeclaration ad = emit_attribute(attr);
        cadc.Add(ad);
    }
}

private static CodeCompileUnit emit_compilation_unit(compilation_unit p) {
    CodeCompileUnit cu = new CodeCompileUnit();
    try {
        emit_compilation_unit0(p, cu);
    } catch (Unsupported u) {
        cu.Namespaces[0].Comments.Add(new CodeCommentStatement("CodeDom Error: " + u.Message));
    }
    return cu;
}

private static CodeCompileUnit emit_compilation_unit0(compilation_unit p, CodeCompileUnit cu) {
    CodeNamespace globals = new CodeNamespace();
    globals.UserData["AST"] = p;
    cu.Namespaces.Add(globals);

    cu.UserData["AST"] = p;
    foreach (using_directive k in p.using_directives) {
        CodeNamespaceImport s = emit_using_directive(k);
        globals.Imports.Add(s);
    }
    cu.AssemblyCustomAttributes.AddRange(emit_attribute_sections(p.attributes));
    foreach (declaration k in p.declarations) {
        if (k is namespace_declaration) {
            CodeNamespace ns = emit_namespace_declaration((namespace_declaration) k);
            cu.Namespaces.Add(ns);
        } else {
            CodeTypeDeclaration td = (CodeTypeDeclaration) emit_declaration(k);
            globals.Types.Add(td);
        }
    }
    return cu;
} // emit_compilation_unit

private static string dotted2string(dotted_name p) {
    return ((p.left != null) ? dotted2string(p.left) + "." : "") + p.right.str;
} // dotted2string

private static CodeTypeReference emit_type(type p) {
    if (p is name_type)
        return emit_name_type((name_type) p);
    if (p is bool_type)
        return emit_bool_type((bool_type) p);
    if (p is decimal_type)
        return emit_decimal_type((decimal_type) p);
    if (p is sbyte_type)
        return emit_sbyte_type((sbyte_type) p);
    if (p is byte_type)
        return emit_byte_type((byte_type) p);
    if (p is short_type)
        return emit_short_type((short_type) p);
    if (p is ushort_type)
        return emit_ushort_type((ushort_type) p);
    if (p is int_type)
        return emit_int_type((int_type) p);
    if (p is uint_type)
        return emit_uint_type((uint_type) p);
    if (p is long_type)
        return emit_long_type((long_type) p);
    if (p is ulong_type)
        return emit_ulong_type((ulong_type) p);
    if (p is char_type)
        return emit_char_type((char_type) p);
    if (p is float_type)
        return emit_float_type((float_type) p);
    if (p is double_type)
        return emit_double_type((double_type) p);
    if (p is object_type)
        return emit_object_type((object_type) p);
    if (p is string_type)
        return emit_string_type((string_type) p);
    if (p is array_type)
        return emit_array_type((array_type) p);
    if (p is void_type)
        return emit_void_type((void_type) p);
    if (p is pointer_type)
        return emit_pointer_type((pointer_type) p);
    if (p is void_pointer_type)
        return emit_void_pointer_type((void_pointer_type) p);
    throw new Unsupported(p.ToString());
} // emit_type

private static CodeTypeReference emit_bool_type(bool_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(bool));
    tr.UserData["AST"] = p;
    return tr;
} // emit_bool_type

private static CodeTypeReference emit_decimal_type(decimal_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(decimal));
    tr.UserData["AST"] = p;
    return tr;
} // emit_decimal_type

private static CodeTypeReference emit_sbyte_type(sbyte_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(sbyte));
    tr.UserData["AST"] = p;
    return tr;
} // emit_sbyte_type

private static CodeTypeReference emit_byte_type(byte_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(byte));
    tr.UserData["AST"] = p;
    return tr;
} // emit_byte_type

private static CodeTypeReference emit_short_type(short_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(short));
    tr.UserData["AST"] = p;
    return tr;
} // emit_short_type

private static CodeTypeReference emit_ushort_type(ushort_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(ushort));
    tr.UserData["AST"] = p;
    return tr;
} // emit_ushort_type

private static CodeTypeReference emit_int_type(int_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(int));
    tr.UserData["AST"] = p;
    return tr;
} // emit_int_type

private static CodeTypeReference emit_uint_type(uint_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(uint));
    tr.UserData["AST"] = p;
    return tr;
} // emit_uint_type

private static CodeTypeReference emit_long_type(long_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(long));
    tr.UserData["AST"] = p;
    return tr;
} // emit_long_type

private static CodeTypeReference emit_ulong_type(ulong_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(ulong));
    tr.UserData["AST"] = p;
    return tr;
} // emit_ulong_type

private static CodeTypeReference emit_char_type(char_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(char));
    tr.UserData["AST"] = p;
    return tr;
} // emit_char_type

private static CodeTypeReference emit_float_type(float_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(float));
    tr.UserData["AST"] = p;
    return tr;
} // emit_float_type

private static CodeTypeReference emit_double_type(double_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(double));
    tr.UserData["AST"] = p;
    return tr;
} // emit_double_type

private static CodeTypeReference emit_object_type(object_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(object));
    tr.UserData["AST"] = p;
    return tr;
} // emit_object_type

private static CodeTypeReference emit_string_type(string_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(string));
    tr.UserData["AST"] = p;
    return tr;
} // emit_string_type

private static CodeTypeReference emit_array_type(array_type p) {
    CodeTypeReference t0 = emit_type(p.ty);
    CodeTypeReference tr = new CodeTypeReference(t0, p.rank_specifier);
    tr.UserData["AST"] = p;
    return tr;
} // emit_array_type

private static CodeExpression emit_argument(argument p) {
    CodeExpression e = emit_expression(p.expr);
    if (p.kind != null) {
        switch (p.kind.tag) {
        case "ref":
            e = new CodeDirectionExpression(FieldDirection.Ref, e);
            e.UserData["AST"] = p;
            break;
        case "out":
            e = new CodeDirectionExpression(FieldDirection.Out, e);
            e.UserData["AST"] = p;
            break;
        default:
            throw new Unsupported("CodeDOM does not support: " + p.kind.tag);
        }
    }
    return e;
} // emit_argument

private static CodeExpression emit_expression(expression p) {
    if (p is simple_name)
        return emit_simple_name_expr((simple_name) p);
    if (p is literal)
        return emit_literal((literal) p);
    if (p is member_access)
        return emit_member_access((member_access) p);
    if (p is invocation_expression)
        return emit_invocation_expression((invocation_expression) p);
    if (p is element_access)
        return emit_element_access((element_access) p);
    if (p is this_access)
        return emit_this_access((this_access) p);
    if (p is base_access)
        return emit_base_access((base_access) p);
    if (p is post_expression)
        return emit_post_expression((post_expression) p);
    if (p is new_expression)
        return emit_new_expression((new_expression) p);
    if (p is array_creation_expression1)
        return emit_array_creation_expression1((array_creation_expression1) p);
    if (p is array_creation_expression2)
        return emit_array_creation_expression2((array_creation_expression2) p);
    if (p is typeof_expression)
        return emit_typeof_expression((typeof_expression) p);
    if (p is checked_expression)
        return emit_checked_expression((checked_expression) p);
    if (p is unchecked_expression)
        return emit_unchecked_expression((unchecked_expression) p);
    if (p is unary_expression)
        return emit_unary_expression((unary_expression) p);
    if (p is pre_expression)
        return emit_pre_expression((pre_expression) p);
    if (p is cast_expression)
        return emit_cast_expression((cast_expression) p);
    if (p is binary_expression)
        return emit_binary_expression((binary_expression) p);
    if (p is is_expression)
        return emit_is_expression((is_expression) p);
    if (p is as_expression)
        return emit_as_expression((as_expression) p);
    if (p is cond_expression)
        return emit_cond_expression((cond_expression) p);
    if (p is assignment_expression)
        return emit_assignment_expression((assignment_expression) p);
    if (p is compound_assignment_expression)
        return emit_compound_assignment_expression((compound_assignment_expression) p);
    if (p is sizeof_expression)
        return emit_sizeof_expression((sizeof_expression) p);
    if (p is implicit_cast_expression)
        return emit_implicit_cast_expression((implicit_cast_expression) p);
    throw new Unsupported(p.ToString());
} // emit_expression

private static CodeExpression emit_literal(literal p) {
    if (p is integer_literal)
        return emit_integer_literal((integer_literal) p);
    if (p is real_literal)
        return emit_real_literal((real_literal) p);
    if (p is character_literal)
        return emit_character_literal((character_literal) p);
    if (p is string_literal)
        return emit_string_literal((string_literal) p);
    if (p is boolean_literal)
        return emit_boolean_literal((boolean_literal) p);
    if (p is null_literal)
        return emit_null_literal((null_literal) p);
    throw new Unsupported(p.ToString());
} // emit_literal

private static CodePrimitiveExpression emit_integer_literal(integer_literal p) {
    CodePrimitiveExpression pe = new CodePrimitiveExpression(p.value);
    pe.UserData["AST"] = p;
    return pe;
} // emit_integer_literal

private static CodePrimitiveExpression emit_real_literal(real_literal p) {
    CodePrimitiveExpression pe = new CodePrimitiveExpression(p.value);
    pe.UserData["AST"] = p;
    return pe;
} // emit_real_literal

private static CodePrimitiveExpression emit_character_literal(character_literal p) {
    CodePrimitiveExpression pe = new CodePrimitiveExpression(p.value);
    pe.UserData["AST"] = p;
    return pe;
} // emit_character_literal

private static CodePrimitiveExpression emit_string_literal(string_literal p) {
    CodePrimitiveExpression pe = new CodePrimitiveExpression(p.value);
    pe.UserData["AST"] = p;
    return pe;
} // emit_string_literal

private static CodePrimitiveExpression emit_boolean_literal(boolean_literal p) {
    CodePrimitiveExpression pe = new CodePrimitiveExpression(p.value);
    pe.UserData["AST"] = p;
    return pe;
} // emit_boolean_literal

private static CodePrimitiveExpression emit_null_literal(null_literal p) {
    CodePrimitiveExpression pe = new CodePrimitiveExpression(p.value);
    pe.UserData["AST"] = p;
    return pe;
} // emit_null_literal

private static CodeExpression emit_member_access(member_access p) {
    if (p is expr_access)
        return emit_expr_access((expr_access) p);
    if (p is pointer_access)
        return emit_pointer_access((pointer_access) p);
    if (p is predefined_access)
        return emit_predefined_access((predefined_access) p);
    throw new Unsupported(p.ToString());
} // emit_member_access

private static CodeExpression emit_expr_access(expr_access p) {
    CodeExpression e;
    //
    //string ns = null;
    //Type lhsType = null;
    //if (p.expr is simple_name) {
    //  simple_name s = (simple_name) p.expr;
    //  if (s.sym is NameSpace) {
    //      NameSpace n = (NameSpace) s.sym;
    //      ns = n.FullName;
    //  } else if (s.sym is Type) {
    //      lhsType = (Type) s.sym;
    //  }
    //} else if (p.expr is expr_access) {
    //  expr_access ea = (expr_access) p.expr;
    //  if (ea.sym is NameSpace) {
    //      NameSpace n = (NameSpace) ea.sym;
    //      ns = n.FullName;
    //  } else if (ea.sym is Type) {
    //      lhsType = (Type) ea.sym;
    //  }
    //}
    //
    CodeExpression t0 = emit_expression(p.expr);
    string id = p.id.str;
    if (p.sym is ClassType) {
        throw new Unsupported("unhandled ClassType in expr access");
    } else if (p.sym is MethodSuite) {
        e = t0;
    } else if (p.sym is Field) {
        CodeFieldReferenceExpression fre = new CodeFieldReferenceExpression();
        fre.UserData["AST"] = p;
        fre.FieldName = id;
        fre.TargetObject = t0;
        e = fre;
    } else if (p.sym is Property) {
        CodePropertyReferenceExpression pre = new CodePropertyReferenceExpression();
        pre.UserData["AST"] = p;
        pre.PropertyName = id;
        pre.TargetObject = t0;
        e = pre;
    } else {
        throw new Unsupported("unhandled sym type in expr_access");
    }
    return e;
} // emit_expr_access

private static CodeExpression emit_pointer_access(pointer_access p) {
    throw new Unsupported("pointer access not handled");
} // emit_pointer_access

private static CodeExpression emit_predefined_access(predefined_access p) {
    throw new Unsupported("predefined access not handled");
} // emit_predefined_access

private static CodeExpression emit_invocation_expression(invocation_expression p) {
    CodeExpression e = null;
    if (p.method != null) {
        CodeExpression target = null;
        if (p.method.IsInstance) {
            target = emit_expression(p.expr);
        }
        CodeExpressionCollection ec;
        if (p.expr.typ is DelegateType) {
            CodeDelegateInvokeExpression die = new CodeDelegateInvokeExpression();
            die.UserData["AST"] = p;
            die.TargetObject = target;
            ec = die.Parameters;
            e = die;
        } else {
            CodeMethodReferenceExpression mre = new CodeMethodReferenceExpression();
            mre.UserData["AST"] = p;
            mre.TargetObject = target;
            mre.MethodName = p.method.id.str;
            CodeMethodInvokeExpression mie = new CodeMethodInvokeExpression();
            mie.UserData["AST"] = p;
            mie.Method = mre;
            ec = mie.Parameters;
            e = mie;
        }
        emit_argumentList(p.args, ec);
    }
    return e;
} // emit_invocation_expression

private static CodeExpression emit_element_access(element_access p) {
    CodeExpression t0 = emit_expression(p.expr);
    if (p.expr.typ is ArrayType) {
        CodeArrayIndexerExpression aie = new CodeArrayIndexerExpression();
        aie.UserData["AST"] = p;
        aie.TargetObject = t0;
        emit_argumentList(p.exprs, aie.Indices);
        return aie;
    } else {
        CodeIndexerExpression aie = new CodeIndexerExpression();
        aie.UserData["AST"] = p;
        aie.TargetObject = t0;
        emit_argumentList(p.exprs, aie.Indices);
        return aie;
    }
} // emit_element_access

private static void emit_argumentList(argumentList aList, CodeExpressionCollection ec) {
    foreach (argument k in aList) {
        CodeExpression s = emit_argument(k);
        ec.Add(s);
    }
}

private static CodeThisReferenceExpression emit_this_access(this_access p) {
    CodeThisReferenceExpression tre = new CodeThisReferenceExpression();
    tre.UserData["AST"] = p;
    return tre;
} // emit_this_access

private static CodeBaseReferenceExpression emit_base_access(base_access p) {
    CodeBaseReferenceExpression bre = new CodeBaseReferenceExpression();
    bre.UserData["AST"] = p;
    return bre;
} // emit_base_access

private static CodeExpression emit_post_expression(post_expression p) {
    throw new Unsupported("post expression not handled");
} // emit_post_expression

private static CodeExpression emit_new_expression(new_expression p) {
    CodeTypeReference t0 = emit_type(p.ty);
    CodeExpression e;

    if (p.typ is DelegateType) {
        CodeDelegateCreateExpression dce = new CodeDelegateCreateExpression();
        dce.UserData["AST"] = p;
        dce.DelegateType = t0;
        argument a = p.args[0];
        if (a.expr is expr_access) {
            expr_access ea = (expr_access) a.expr;
            CodeExpression o = emit_expression(ea.expr);
            dce.TargetObject = o;
            dce.MethodName = ea.id.str;
            e = dce;
        } else {
            throw new Unsupported("unknown expr in new_expression: " + a.expr.ToString());
        }
    } else if (p.typ is ClassType || p.typ is StructType) {
        CodeObjectCreateExpression oce = new CodeObjectCreateExpression();
        oce.UserData["AST"] = p;
        oce.CreateType = t0;
        emit_argumentList(p.args, oce.Parameters);
        e = oce;
    } else {
        throw new Unsupported("unknown type in new_expression: " + p.typ.ToString());
    }

    return e;
} // emit_new_expression

private static CodeExpression emit_array_creation_expression1(array_creation_expression1 p) {
    if (p.exprs.Count > 1) {
        throw new Unsupported("cannot handle multi-dimension arrays");
    }
    if (p.ranks.Count > 0) {
        throw new Unsupported("cannot handle high-rank arrays");
    }

    CodeArrayCreateExpression ace = new CodeArrayCreateExpression();
    ace.UserData["AST"] = p;
    CodeTypeReference t0 = emit_type(p.ty);
    ace.CreateType = t0;
    if (p.init != null) {
        emit_array_initializer(p.init, ace.Initializers);
    } else {
        CodeExpression expr = emit_expression(p.exprs[0]);
        ace.SizeExpression = expr;
    }
    return ace;
} // emit_array_creation_expression1

private static CodeArrayCreateExpression emit_array_creation_expression2(array_creation_expression2 p) {
    CodeArrayCreateExpression ace = new CodeArrayCreateExpression();
    ace.UserData["AST"] = p;
    CodeTypeReference t0 = emit_type(p.ty);
    ace.CreateType = t0;
    emit_array_initializer(p.init, ace.Initializers);
    return ace;
} // emit_array_creation_expression2

private static CodeExpression emit_typeof_expression(typeof_expression p) {
    CodeTypeOfExpression toe = new CodeTypeOfExpression();
    toe.UserData["AST"] = p;
    CodeTypeReference t0 = emit_type(p.ty);
    toe.Type = t0;
    return toe;
} // emit_typeof_expression

private static CodeExpression emit_checked_expression(checked_expression p) {
    throw new Unsupported("unhandled checked expression");
} // emit_checked_expression

private static CodeExpression emit_unchecked_expression(unchecked_expression p) {
    throw new Unsupported("unhandled unchecked expression");
} // emit_unchecked_expression

private static CodeExpression emit_unary_expression(unary_expression p) {
    throw new Unsupported("unhandled unary expression");
} // emit_unary_expression

private static CodeExpression emit_pre_expression(pre_expression p) {
    throw new Unsupported("unhandled prefix expression");
} // emit_pre_expression

private static CodeCastExpression emit_cast_expression(cast_expression p) {
    CodeCastExpression ce = new CodeCastExpression();
    ce.UserData["AST"] = p;
    CodeTypeReference t0 = emit_type(p.ty);
    ce.TargetType = t0;
    CodeExpression t1 = emit_expression(p.expr);
    ce.Expression = t1;
    return ce;
} // emit_cast_expression

private static CodeExpression emit_implicit_cast_expression(implicit_cast_expression p) {
    throw new Unsupported("unhandled implicit cast expression");
}

private static CodeExpression emit_binary_expression(binary_expression p) {
    CodeBinaryOperatorExpression boe = new CodeBinaryOperatorExpression();
    boe.UserData["AST"] = p;
    CodeExpression t0 = emit_expression(p.e1);
    boe.Left = t0;
    CodeBinaryOperatorType op;
    switch (p.op.tag) {
    case "+": op = CodeBinaryOperatorType.Add; break;
    case "=": op = CodeBinaryOperatorType.Assign; break;
    case "&": op = CodeBinaryOperatorType.BitwiseAnd; break;
    case "|": op = CodeBinaryOperatorType.BitwiseOr; break;
    case "&&": op = CodeBinaryOperatorType.BooleanAnd; break;
    case "||": op = CodeBinaryOperatorType.BooleanOr; break;
    case "/": op = CodeBinaryOperatorType.Divide; break;
    case ">": op = CodeBinaryOperatorType.GreaterThan; break;
    case ">=": op = CodeBinaryOperatorType.GreaterThanOrEqual; break;
    case "==": op = CodeBinaryOperatorType.IdentityEquality; break;
    case "!=": op = CodeBinaryOperatorType.IdentityInequality; break;
    case "<": op = CodeBinaryOperatorType.LessThan; break;
    case "<=": op = CodeBinaryOperatorType.LessThanOrEqual; break;
    case "%": op = CodeBinaryOperatorType.Modulus; break;
    case "*": op = CodeBinaryOperatorType.Multiply; break;
    case "-": op = CodeBinaryOperatorType.Subtract; break;
    default:
        throw new Unsupported("unhandled binary operator " + p.op.str);
    }
    boe.Operator = op;
    if (p.op.tag == "==") {
        // WARNING: Could be CodeBinaryOperatorType.ValueEquality
    }
    CodeExpression t2 = emit_expression(p.e2);
    boe.Right = t2;
    return boe;
} // emit_binary_expression

private static CodeExpression emit_is_expression(is_expression p) {
    throw new Unsupported("unhandled 'is' expression");
} // emit_is_expression

private static CodeExpression emit_as_expression(as_expression p) {
    throw new Unsupported("unhandled 'as' expression");
} // emit_as_expression

private static CodeExpression emit_cond_expression(cond_expression p) {
    throw new Unsupported("unhandled cond expression");
} // emit_cond_expression

private static CodeExpression emit_compound_assignment_expression(compound_assignment_expression p) {
    throw new Unsupported("unhandled compound_assignment as expression");
}

private static CodeStatement emit_compound_assignment_statement(compound_assignment_expression p) {
    if (!(p.typ is DelegateType)) {
        throw new Unsupported("unhandled compound assignment expression " + p.op.str);
    }
    CodeEventReferenceExpression eventRef = (CodeEventReferenceExpression) emit_expression(p.e1);
    eventRef.UserData["AST"] = p;
    CodeExpression listener = emit_expression(p.e2);
    if (p.op.str[0] == '+') {
        CodeAttachEventStatement aes = new CodeAttachEventStatement(eventRef, listener);
        aes.UserData["AST"] = p;
        return aes;
    } else if (p.op.str[0] == '-') {
        CodeRemoveEventStatement res = new CodeRemoveEventStatement(eventRef, listener);
        res.UserData["AST"] = p;
        return res;
    } else {
        throw new Unsupported("unknown op: " + p.op.str);
    }
} // emit_compound_assignment_expression

private static CodeExpression emit_assignment_expression(assignment_expression p) {
    throw new Unsupported("unhandled:  assignments as expressions");
}

private static CodeStatement emit_assignment_statement(assignment_expression p) {
    CodeAssignStatement a = new CodeAssignStatement();
    a.UserData["AST"] = p;
    CodeExpression t0 = emit_expression(p.e1);
    a.Left = t0;
    CodeExpression t2 = emit_expression(p.e2);
    a.Right = t2;
    return a;
} // emit_assignment_expression

private static void emit_statement(statement p, CodeStatementCollection sc) {
    sc.Add(emit_statement(p));
}

private static CodeStatement emit_statement(statement p) {
    try {
        return emit_statement0(p);
    } catch (Unsupported u) {
        CodeStatement s = new CodeCommentStatement("CodeDom Error: " + u.Message);
        s.UserData["AST"] = p;
        return s;
    }
}

private static CodeStatement emit_statement0(statement p) {
    if (p is expression_statement)
        return emit_expression_statement((expression_statement) p);
    if (p is block_statement)
        return emit_block_statement((block_statement) p);
    if (p is empty_statement)
        return emit_empty_statement((empty_statement) p);
    if (p is labeled_statement)
        return emit_labeled_statement((labeled_statement) p);
    if (p is local_statement)
        return emit_local_statement((local_statement) p);
    if (p is const_statement)
        return emit_const_statement((const_statement) p);
    if (p is if_statement)
        return emit_if_statement((if_statement) p);
    if (p is switch_statement)
        return emit_switch_statement((switch_statement) p);
    if (p is while_statement)
        return emit_while_statement((while_statement) p);
    if (p is do_statement)
        return emit_do_statement((do_statement) p);
    if (p is for_statement)
        return emit_for_statement((for_statement) p);
    if (p is foreach_statement)
        return emit_foreach_statement((foreach_statement) p);
    if (p is break_statement)
        return emit_break_statement((break_statement) p);
    if (p is continue_statement)
        return emit_continue_statement((continue_statement) p);
    if (p is goto_default_statement)
        return emit_goto_default_statement((goto_default_statement) p);
    if (p is goto_statement)
        return emit_goto_statement((goto_statement) p);
    if (p is goto_case_statement)
        return emit_goto_case_statement((goto_case_statement) p);
    if (p is return_statement)
        return emit_return_statement((return_statement) p);
    if (p is throw_statement)
        return emit_throw_statement((throw_statement) p);
    if (p is try_statement)
        return emit_try_statement((try_statement) p);
    if (p is checked_statement)
        return emit_checked_statement((checked_statement) p);
    if (p is unchecked_statement)
        return emit_unchecked_statement((unchecked_statement) p);
    if (p is lock_statement)
        return emit_lock_statement((lock_statement) p);
    if (p is using_statement)
        return emit_using_statement((using_statement) p);
    if (p is fixed_statement)
        return emit_fixed_statement((fixed_statement) p);
    throw new Unsupported(p.ToString());
} // emit_statement

private static CodeStatement emit_block_statement(block_statement p) {
    throw new Unsupported("unhandled block statement");
} // emit_block_statement

private static void emit_block_statement(block_statement p, CodeStatementCollection sc) {
    foreach (statement k in p.stmts) {
        emit_statement(k, sc);
    }
} // emit_block_statement

private static CodeStatement emit_empty_statement(empty_statement p) {
    CodeCommentStatement cs = new CodeCommentStatement("empty statement");
    cs.UserData["AST"] = p;
    return cs;
} // emit_empty_statement

private static CodeLabeledStatement emit_labeled_statement(labeled_statement p) {
    CodeLabeledStatement ls = new CodeLabeledStatement();
    ls.UserData["AST"] = p;
    ls.Label = p.label.str;
    CodeStatement t1 = emit_statement0(p.stmt);
    ls.Statement = t1;
    return ls;
} // emit_labeled_statement

private static CodeStatement emit_local_statement(local_statement p) {
    if (p.vars.Count > 1) {
        throw new Unsupported("cannot handle multiple declarations");
    }
    CodeTypeReference t2 = emit_type(p.ty);

    var_declarator k = (var_declarator)p.vars[0];
    CodeVariableDeclarationStatement vds = new CodeVariableDeclarationStatement();
    vds.UserData["AST"] = p;
    vds.Type = t2;
    vds.Name = k.id.str;
    if (k.init != null) {
        CodeExpression t4 = emit_variable_initializer(k.init);
        vds.InitExpression = t4;
    }
    return vds;
} // emit_local_statement

private static CodeStatement emit_var_decl(var_declarator p) {
    throw new Unsupported("unhandled var_declarator");
} // emit_var_decl

private static CodeStatement emit_const_statement(const_statement p) {
    throw new Unsupported("unhandled const_statement");
} // emit_const_statement

private static CodeStatement emit_const_decl(const_declarator p) {
    throw new Unsupported("unhandled const_declarator expression");
} // emit_const_decl

private static CodeConditionStatement emit_if_statement(if_statement p) {
    CodeConditionStatement cs = new CodeConditionStatement();
    cs.UserData["AST"] = p;
    CodeExpression t0 = emit_expression(p.expr);
    cs.Condition = t0;
    emit_statement(p.thenpart, cs.TrueStatements);
    if (p.elsepart != null) {
        emit_statement(p.elsepart, cs.FalseStatements);
    }
    return cs;
} // emit_if_statement

private static CodeStatement emit_switch_statement(switch_statement p) {
    throw new Unsupported("unhandled switch statement");
} // emit_switch_statement

private static CodeStatement emit_switch_section(switch_section p) {
    throw new Unsupported("unhandled switch_section");
} // emit_switch_section

private static CodeObject emit_switch_label(switch_label p) {
    if (p is switch_expression)
        return emit_switch_expression((switch_expression) p);
    if (p is switch_default)
        return emit_switch_default((switch_default) p);
    throw new Unsupported(p.ToString());
} // emit_switch_label

private static CodeObject emit_switch_expression(switch_expression p) {
    throw new Unsupported("unhandled switch expression");
} // emit_switch_expression

private static CodeObject emit_switch_default(switch_default p) {
    throw new Unsupported("unhandled switch default");
} // emit_switch_default

private static CodeIterationStatement emit_while_statement(while_statement p) {
    CodeIterationStatement iter = new CodeIterationStatement();
    iter.UserData["AST"] = p;
    iter.TestExpression = emit_expression(p.expr);
    emit_statement(p.body, iter.Statements);
    return iter;
} // emit_while_statement

private static CodeIterationStatement emit_do_statement(do_statement p) {
    throw new Unsupported("unhandled 'do' loop statement");
} // emit_do_statement

private static CodeIterationStatement emit_for_statement(for_statement p) {
    throw new Unsupported("unhandled 'for' loop");
} // emit_for_statement

private static CodeObject emit_for_init(for_init p) {
    if (p is for_decl)
        return emit_for_decl((for_decl) p);
    if (p is for_list)
        return emit_for_list((for_list) p);
    throw new Unsupported(p.ToString());
} // emit_for_init

private static CodeObject emit_for_decl(for_decl p) {
    throw new Unsupported("unhandled 'for' decl");
} // emit_for_decl

private static CodeObject emit_for_list(for_list p) {
    throw new Unsupported("unhandled 'for' list");
} // emit_for_list

private static CodeStatement emit_foreach_statement(foreach_statement p) {
    throw new Unsupported("unhandled 'foreach' loop");
} // emit_foreach_statement

private static CodeStatement emit_break_statement(break_statement p) {
    throw new Unsupported("unhandled break statement");
} // emit_break_statement

private static CodeStatement emit_continue_statement(continue_statement p) {
    throw new Unsupported("unhandled continue statement");
} // emit_continue_statement

private static CodeStatement emit_goto_default_statement(goto_default_statement p) {
    throw new Unsupported("unhandled goto default");
} // emit_goto_default_statement

private static CodeGotoStatement emit_goto_statement(goto_statement p) {
    return new CodeGotoStatement(p.id.str);
} // emit_goto_statement

private static CodeStatement emit_goto_case_statement(goto_case_statement p) {
    throw new Unsupported("unhandled goto case");
} // emit_goto_case_statement

private static CodeMethodReturnStatement emit_return_statement(return_statement p) {
    CodeMethodReturnStatement mrs = new CodeMethodReturnStatement();
    mrs.UserData["AST"] = p;
    if (p.expr != null) {
        mrs.Expression = emit_expression(p.expr);
    }
    return mrs;
} // emit_return_statement

private static CodeThrowExceptionStatement emit_throw_statement(throw_statement p) {
    CodeThrowExceptionStatement tes = new CodeThrowExceptionStatement();
    tes.UserData["AST"] = p;
    tes.ToThrow = emit_expression(p.expr);
    return tes;
} // emit_throw_statement

private static CodeTryCatchFinallyStatement emit_try_statement(try_statement p) {
    CodeTryCatchFinallyStatement tcfs = new CodeTryCatchFinallyStatement();
    tcfs.UserData["AST"] = p;
    emit_block_statement((block_statement)p.block, tcfs.TryStatements);
    if (p.catches != null) {
        CodeCatchClauseCollection ccc = emit_catch_clauses(p.catches);
        tcfs.CatchClauses.AddRange(ccc);
    }
    if (p.finally_block != null) {
        emit_block_statement((block_statement)p.finally_block.block, tcfs.FinallyStatements);
    }
    return tcfs;
} // emit_try_statement

private static CodeCatchClause emit_catch_clause(catch_clause p) {
    return emit_specific_catch_clause(p);
} // emit_catch_clause

private static CodeCatchClause emit_specific_catch_clause(catch_clause p) {
    CodeCatchClause cc = new CodeCatchClause(); // Why doesn't this have UserData["AST"]????
    cc.CatchExceptionType = emit_type(p.ty);
    if (p.id != null) {
        cc.LocalName = p.id.str;
    }
    emit_block_statement((block_statement) p.block, cc.Statements);
    return cc;
} // emit_specific_catch_clause

private static CodeCatchClause emit_general_catch_clause(statement p) {
    CodeCatchClause cc = new CodeCatchClause();
    emit_statement(p, cc.Statements);
    return cc;
} // emit_general_catch_clause

private static CodeCatchClauseCollection emit_catch_clauses(catch_clauses p) {
    CodeCatchClauseCollection ccc = new CodeCatchClauseCollection();
    foreach (catch_clause k in p.specifics) {
        CodeCatchClause s = emit_catch_clause(k);
        ccc.Add(s);
    }
    if (p.general != null) {
        CodeCatchClause t1 = emit_general_catch_clause(p.general);
        ccc.Add(t1);
    }
    return ccc;
} // emit_catch_clauses

private static CodeStatement emit_checked_statement(checked_statement p) {
    throw new Unsupported("unhandled checked statement");
} // emit_checked_statement

private static CodeStatement emit_unchecked_statement(unchecked_statement p) {
    throw new Unsupported("unhandled unchecked statement");
} // emit_unchecked_statement

private static CodeStatement emit_lock_statement(lock_statement p) {
    throw new Unsupported("unhandled lock statement");
} // emit_lock_statement

private static CodeStatement emit_using_statement(using_statement p) {
    throw new Unsupported("unhandled using statement");
} // emit_using_statement

private static CodeObject emit_resource(resource p) {
    if (p is resource_expr)
        return emit_resource_expr((resource_expr) p);
    if (p is resource_decl)
        return emit_resource_decl((resource_decl) p);
    throw new Unsupported(p.ToString());
} // emit_resource

private static CodeExpression emit_resource_expr(resource_expr p) {
    throw new Unsupported("unhandled 'resource expression");
} // emit_resource_expr

private static CodeExpression emit_resource_decl(resource_decl p) {
    throw new Unsupported("unhandled resource decl");
} // emit_resource_decl

private static CodeTypeMember emit_declaration(declaration p) {
    if (p is constant_declaration)
        return emit_constant_declaration((constant_declaration) p);
    if (p is field_declaration)
        return emit_field_declaration((field_declaration) p);
    if (p is method_declaration)
        return emit_method_declaration((method_declaration) p);
    if (p is property_declaration)
        return emit_property_declaration((property_declaration) p);
    if (p is event_declaration1)
        return emit_event_declaration1((event_declaration1) p);
    if (p is event_declaration2)
        return emit_event_declaration2((event_declaration2) p);
    if (p is indexer_declaration)
        return emit_indexer_declaration((indexer_declaration) p);
    if (p is operator_declaration)
        return emit_operator_declaration((operator_declaration) p);
    if (p is constructor_declaration)
        return emit_constructor_declaration((constructor_declaration) p);
    if (p is destructor_declaration)
        return emit_destructor_declaration((destructor_declaration) p);
    if (p is struct_declaration)
        return emit_struct_declaration((struct_declaration) p);
    if (p is interface_declaration)
        return emit_interface_declaration((interface_declaration) p);
    if (p is interface_method_declaration)
        return emit_interface_method_declaration((interface_method_declaration) p);
    if (p is interface_property_declaration)
        return emit_interface_property_declaration((interface_property_declaration) p);
    if (p is interface_event_declaration)
        return emit_interface_event_declaration((interface_event_declaration) p);
    if (p is interface_indexer_declaration)
        return emit_interface_indexer_declaration((interface_indexer_declaration) p);
    if (p is enum_declaration)
        return emit_enum_declaration((enum_declaration) p);
    if (p is class_declaration)
        return emit_class_declaration((class_declaration) p);
    if (p is delegate_declaration)
        return emit_delegate_declaration((delegate_declaration) p);
    throw new Unsupported(p.ToString());
} // emit_declaration

private static CodeNamespace emit_namespace_declaration(namespace_declaration p) {
    CodeNamespace n = new CodeNamespace();
    n.UserData["AST"] = p;
    string t0 = dotted2string(p.id);
    n.Name = t0;
    emit_namespace_body(p.nb, n);
    return n;
} // emit_namespace_declaration

private static void emit_namespace_body(namespace_body p, CodeNamespace n) {
    foreach (using_directive k in p.ud) {
        CodeNamespaceImport s = emit_using_directive(k);
        n.Imports.Add(s);
    }
    foreach (declaration k in p.declarations) {
        if (k is namespace_declaration) {
            throw new Unsupported("nested namespace declarations unallowed");
        } else {
            CodeTypeDeclaration s = (CodeTypeDeclaration) emit_declaration(k);
            n.Types.Add(s);
        }
    }
} // emit_namespace_body

private static CodeNamespaceImport emit_using_directive(using_directive p) {
    if (p is alias_directive)
        return emit_alias_directive((alias_directive) p);
    if (p is namespace_directive)
        return emit_namespace_directive((namespace_directive) p);
    throw new Unsupported(p.ToString());
} // emit_using_directive

private static CodeNamespaceImport emit_alias_directive(alias_directive p) {
    throw new Unsupported("\t// ERROR: CodeDOM does not support: \"using A=B;\"\n");
} // emit_alias_directive

private static CodeNamespaceImport emit_namespace_directive(namespace_directive p) {
    CodeNamespaceImport ni = new CodeNamespaceImport();
    ni.UserData["AST"] = p;
    string t0 = dotted2string(p.name);
    ni.Namespace = t0;
    return ni;
} // emit_namespace_directive

private static CodeTypeDeclaration emit_constant_declaration(constant_declaration p) {
    throw new Unsupported("unhandled const declaration");
} // emit_constant_declaration

private static CodeMemberField emit_field_declaration(field_declaration p) {
    if (p.decls.Count > 1) {
        throw new Unsupported("cannot handle compound field declarations");
    }
    System.Collections.Queue t3 = new System.Collections.Queue();
    field_declarator k = (field_declarator) p.decls[0];
    CodeMemberField mf = new CodeMemberField();
    mf.UserData["AST"] = p;
    mf.CustomAttributes = emit_attribute_sections(p.attrs);
    CodeTypeReference t2 = emit_type(p.ty);
    mf.Type = t2;
    mf.Name = k.id.str;
    if (k.init != null) {
        CodeExpression t4 = emit_variable_initializer(k.init);
        mf.InitExpression = t4;
    }
    mf.Attributes = emit_CodeDomAttributes(p.mods);
    return mf;
} // emit_field_declaration

private static CodeMemberMethod emit_method_declaration(method_declaration p) {
    CodeMemberMethod mm = new CodeMemberMethod();
    mm.UserData["AST"] = p;
    mm.Attributes = emit_CodeDomAttributes(p.mods);
    mm.CustomAttributes = emit_attribute_sections(p.attrs);
    mm.ReturnType = emit_type(p.ty);
    // WARNING: unimplemented Interface name: method_declaration.name
    mm.Name = p.name.id.str;
    mm.Parameters.AddRange(emit_formals(p.parms));
    if (p.body != null) {
        emit_block_statement((block_statement)p.body, mm.Statements);
    } else {
        // WARNING: unimplemented null check: method_declaration.body
    }
    return mm;
} // emit_method_declaration

private static CodeTypeReference emit_void_type(void_type p) {
    CodeTypeReference tr = new CodeTypeReference(typeof(void));
    tr.UserData["AST"] = p;
    return tr;
} // emit_void_type

private static CodeParameterDeclarationExpressionCollection emit_formals(formals p) {
    CodeParameterDeclarationExpressionCollection pdec = new CodeParameterDeclarationExpressionCollection();
    foreach (parameter k in p.fixeds) {
        CodeParameterDeclarationExpression s = emit_parameter(k);
        pdec.Add(s);
    }
    if (p.param != null) {
        CodeParameterDeclarationExpression s = emit_parameter(p.param);
        pdec.Add(s);
    }
    return pdec;
} // emit_formals

private static CodeParameterDeclarationExpression emit_parameter(parameter p) {
    if (p is fixed_parameter)
        return emit_fixed_parameter((fixed_parameter) p);
    if (p is params_parameter)
        return emit_params_parameter((params_parameter) p);
    if (p is arglist_parameter)
        return emit_arglist_parameter((arglist_parameter) p);
    throw new Unsupported(p.ToString());
} // emit_parameter

private static CodeParameterDeclarationExpression emit_fixed_parameter(fixed_parameter p) {
    CodeParameterDeclarationExpression pde = new CodeParameterDeclarationExpression();
    pde.UserData["AST"] = p;
    pde.Name = p.id.str;

    pde.CustomAttributes = emit_attribute_sections(p.attrs);
    if (p.mod != null) {
        switch (p.mod.str) {
        case "ref": pde.Direction = FieldDirection.Ref; break;
        case "out": pde.Direction = FieldDirection.Out; break;
        default:
            throw new Unsupported("unhandled modifier " + p.mod.str);
        }
    }
    pde.Type = emit_type(p.ty);
    return pde;
} // emit_fixed_parameter

private static CodeParameterDeclarationExpression emit_params_parameter(params_parameter p) {
    throw new Unsupported("unhandled params declaration");
} // emit_params_parameter

private static CodeParameterDeclarationExpression emit_arglist_parameter(arglist_parameter p) {
    throw new Unsupported("unhandled arglist declaration");
} // emit_arglist_parameter

private static CodeMemberProperty emit_property_declaration(property_declaration p) {
    CodeMemberProperty mp = new CodeMemberProperty();
    mp.UserData["AST"] = p;

    mp.CustomAttributes = emit_attribute_sections(p.attrs); // need to fix this all over the place
    mp.Attributes = emit_CodeDomAttributes(p.mods);
    mp.Type = emit_type(p.ty);
    mp.Name = get_member_name(p.name);
    foreach (accessor_declaration k in p.decls) {
        if (k != null) {
            emit_accessor_declaration(k, mp);
        }
    }
    return mp;
} // emit_property_declaration

private static void emit_accessor_declaration(accessor_declaration p, CodeMemberProperty mp) {
    if (p.attrs.Count > 0) {
        throw new Unsupported("cannot handle attributes");
    }
    switch (p.id.str) {
    default:
        throw new Unsupported("unknown accessor: " + p.id.str);
    case "get":
        mp.HasGet = true;
        if (p.body != null) {
            emit_block_statement((block_statement)p.body, mp.GetStatements);
        }
        break;
    case "set":
        mp.HasSet = true;
        if (p.body != null) {
            emit_block_statement((block_statement)p.body, mp.SetStatements);
        }
        break;
    }
} // emit_accessor_declaration

private static string emit_event_declarator(event_declarator p) {
    return p.id.str;
}

private static CodeMemberEvent emit_event_declaration1(event_declaration1 p) {
    if (p.decls.Count > 1) {
        // WARNING: cannot handle multiple comma-separated events
    }
    declarator d = p.decls[0];
    CodeMemberEvent me = new CodeMemberEvent();
    me.UserData["AST"] = p;
    me.CustomAttributes = emit_attribute_sections(p.attrs);
    me.Type = emit_type(p.ty);
    me.Name = d.id.str;
    me.Attributes = emit_CodeDomAttributes(p.mods);
    return me;
} // emit_event_declaration1

private static CodeMemberEvent emit_event_declaration2(event_declaration2 p) {
    if (p.accessors.Count > 0) {
        throw new Unsupported("cannot handle event accessors");
    }
    CodeMemberEvent me = new CodeMemberEvent();
    me.UserData["AST"] = p;
    me.CustomAttributes = emit_attribute_sections(p.attrs);
    me.Attributes = emit_CodeDomAttributes(p.mods);
    me.Type = emit_type(p.ty);
    me.Name = p.name.id.str;
    // handle accessors here.
    return me;
} // emit_event_declaration2

private static CodeObject emit_event_accessor(event_accessor p) {
    throw new Unsupported("cannot handle event accessors");
} // emit_event_accessor

private static CodeTypeMember emit_indexer_declaration(indexer_declaration p) {
    throw new Unsupported("unhandled indexer declaration");
} // emit_indexer_declaration

private static CodeObject emit_indexer(indexer p) {
    throw new Unsupported("unhandled indexer");
} // emit_indexer

private static CodeTypeMember emit_operator_declaration(operator_declaration p) {
    throw new Unsupported("unhandled operator declaration");
} // emit_operator_declaration

private static CodeTypeMember emit_operator_declarator(operator_declarator p) {
    if (p is unary_declarator)
        return emit_unary_declarator((unary_declarator) p);
    if (p is binary_declarator)
        return emit_binary_declarator((binary_declarator) p);
    if (p is implicit_declarator)
        return emit_implicit_declarator((implicit_declarator) p);
    if (p is explicit_declarator)
        return emit_explicit_declarator((explicit_declarator) p);
    throw new Unsupported(p.ToString());
} // emit_operator_declarator

private static CodeTypeMember emit_unary_declarator(unary_declarator p) {
    throw new Unsupported("unhandled unary declaration");
} // emit_unary_declarator

private static CodeTypeMember emit_binary_declarator(binary_declarator p) {
    throw new Unsupported("unhandled binary declaration");
} // emit_binary_declarator

private static CodeTypeMember emit_implicit_declarator(implicit_declarator p) {
    throw new Unsupported("unhandled implicit declaration");
} // emit_implicit_declarator

private static CodeTypeMember emit_explicit_declarator(explicit_declarator p) {
    throw new Unsupported("unhandled explicit declaration");
} // emit_explicit_declarator

private static CodeMemberMethod emit_constructor_declaration(constructor_declaration p) {
    CodeMemberMethod c;
    if (p.sym.IsStatic) {
        CodeTypeConstructor ctc = new CodeTypeConstructor();
        ctc.UserData["AST"] = p;
        c = ctc;
        emit_constructor_declarator(p.decl, ctc);
    } else {
        CodeConstructor cc = new CodeConstructor();
        cc.UserData["AST"] = p;
        c = cc;
        emit_constructor_declarator(p.decl, cc);
    }
    c.CustomAttributes = emit_attribute_sections(p.attrs);
    c.Attributes = emit_CodeDomAttributes(p.mods);
    if (p.block != null) {
        emit_block_statement((block_statement)p.block, c.Statements);
    } else {
        // WARNING: unimplemented null check: constructor_declaration.block
    }
    return c;
} // emit_constructor_declaration

private static MemberAttributes emit_CodeDomAttributes(System.Collections.IList a) {
    MemberAttributes ma = 0;
    foreach (InputElement e in a) {
        ma |= emit_CodeDomAttribute(e.tag);
    }
    return ma;
}
private static MemberAttributes emit_CodeDomAttribute(string modifier) {
    switch (modifier) {
    case "public":      return MemberAttributes.Public;
    case "abstract":    return MemberAttributes.Abstract;
    case "final":       return MemberAttributes.Final;
    case "override":    return MemberAttributes.Override;
    case "private":     return MemberAttributes.Private;
    case "static":      return MemberAttributes.Static;
    default:
        throw new Unsupported("unhandled non-CodeDOM modifier: " + modifier);
    }
}

private static void emit_constructor_declarator(constructor_declarator p, CodeTypeConstructor c) {
    c.Name = p.id.str;
    c.Parameters.AddRange(emit_formals(p.f));
    // assert(p.init == null)
} // emit_constructor_declarator

private static void emit_constructor_declarator(constructor_declarator p, CodeConstructor c) {
    c.Name = p.id.str;
    c.Parameters.AddRange(emit_formals(p.f));
    if (p.init != null) {
        emit_constructor_initializer(p.init, c);
    }
} // emit_constructor_declarator

private static void emit_constructor_initializer(constructor_initializer p, CodeConstructor c) {
    if (p is base_initializer) {
        emit_base_initializer((base_initializer) p, c);
        return;
    }
    if (p is this_initializer) {
        emit_this_initializer((this_initializer) p, c);
        return;
    }
    throw new Unsupported(p.ToString());
} // emit_constructor_initializer

private static void emit_base_initializer(base_initializer p, CodeConstructor c) {
    emit_argumentList(p.args, c.BaseConstructorArgs);
} // emit_base_initializer

private static void emit_this_initializer(this_initializer p, CodeConstructor c) {
    emit_argumentList(p.args, c.ChainedConstructorArgs);
} // emit_this_initializer

private static CodeTypeMember emit_destructor_declaration(destructor_declaration p) {
    throw new Unsupported("unhandled destructor declaration");
} // emit_destructor_declaration

private static CodeTypeDeclaration emit_struct_declaration(struct_declaration p) {
    CodeTypeDeclaration td = new CodeTypeDeclaration();
    td.UserData["AST"] = p;
    td.IsStruct = true;
    td.CustomAttributes = emit_attribute_sections(p.attrs);
    td.Attributes = emit_CodeDomAttributes(p.mods);
    td.Name = p.id.str;
    foreach (type k in p.interfaces) {
        td.BaseTypes.Add(emit_type(k));
    }
    foreach (declaration k in p.body) {
        td.Members.Add(emit_declaration(k));
    }
    return td;
} // emit_struct_declaration

private static CodeTypeDeclaration emit_interface_declaration(interface_declaration p) {
    CodeTypeDeclaration td = new CodeTypeDeclaration();
    td.UserData["AST"] = p;
    td.IsInterface = true;
    td.CustomAttributes = emit_attribute_sections(p.attrs);
    td.Attributes = emit_CodeDomAttributes(p.mods);
    td.Name = p.id.str;
    foreach (type k in p.interfaces) {
        td.BaseTypes.Add(emit_type(k));
    }
    foreach (declaration k in p.body) {
        td.Members.Add(emit_declaration(k));
    }
    return td;
} // emit_interface_declaration

private static CodeMemberMethod emit_interface_method_declaration(interface_method_declaration p) {
    throw new Unsupported("unhandled interface method declaration");
} // emit_interface_method_declaration

private static CodeMemberProperty emit_interface_property_declaration(interface_property_declaration p) {
    throw new Unsupported("unhandled interface property declaration");
} // emit_interface_property_declaration

private static CodeMemberEvent emit_interface_event_declaration(interface_event_declaration p) {
    throw new Unsupported("unhandled interface event declaration");
} // emit_interface_event_declaration

private static CodeTypeMember emit_interface_indexer_declaration(interface_indexer_declaration p) {
    throw new Unsupported("unhandled interface indexer declaration");
} // emit_interface_indexer_declaration

private static CodeTypeMember emit_enum_declaration(enum_declaration p) {
    throw new Unsupported("unhandled interface enum declaration");
} // emit_enum_declaration

private static CodeTypeDeclaration emit_class_declaration(class_declaration p) {
    CodeTypeDeclaration td = new CodeTypeDeclaration();
    td.UserData["AST"] = p;
    td.IsClass = true;
    td.CustomAttributes.AddRange(emit_attribute_sections(p.attrs));
    td.Attributes = emit_CodeDomAttributes(p.mods);
    td.Name = p.id.str;
    foreach (type k in p.bases) {
        td.BaseTypes.Add(emit_type(k));
    }
    foreach (declaration k in p.body) {
        td.Members.Add(emit_declaration(k));
    }
    return td;
} // emit_class_declaration

private static CodeTypeMember emit_enum_member_declaration(enum_member_declaration p) {
    throw new Unsupported("unhandled enum member declaration");
} // emit_enum_member_declaration

private static CodeTypeDelegate emit_delegate_declaration(delegate_declaration p) {
    CodeTypeDelegate td = new CodeTypeDelegate();
    td.UserData["AST"] = p;
    td.CustomAttributes.AddRange(emit_attribute_sections(p.attrs));
    td.Attributes = emit_CodeDomAttributes(p.mods);
    td.ReturnType = emit_type(p.ty);
    td.Name = p.id.str;
    td.Parameters.AddRange(emit_formals(p.f));
    return td;
} // emit_delegate_declaration

private static CodeAttributeDeclarationCollection emit_attribute_section(attribute_section p) {
    CodeAttributeDeclarationCollection adc = new CodeAttributeDeclarationCollection();
    if (p.target != null) {
        // WARNING: unimplemented target: attribute_section.target
    } else {
        // WARNING: unimplemented null check: attribute_section.target
    }
    foreach (attribute k in p.attributes) {
        adc.Add(emit_attribute(k));
    }
    return adc;
} // emit_attribute_section

private static CodeAttributeDeclaration emit_attribute(attribute p) {
    CodeAttributeDeclaration ad = new CodeAttributeDeclaration();   // Why doesn't CodeAttributeDeclaration have UserData["AST"]?
    CodeTypeReference t0 = emit_type(p.name);
    ad.Name = t0.BaseType;  // WARNING:  Is this correct?
    foreach (expression k in p.arguments.args) {
        CodeAttributeArgument aa = new CodeAttributeArgument(); // UserData["AST"]?
        aa.Value = emit_expression(k);
        ad.Arguments.Add(aa);
    }
    // p.arguments.namedargs
    foreach (named_argument s in p.arguments.namedargs) {
        CodeAttributeArgument aa = emit_named_argument(s);
        ad.Arguments.Add(aa);
    }
    return ad;
} // emit_attribute

private static CodeAttributeArgument emit_named_argument(named_argument p) {
    CodeAttributeArgument aa = new CodeAttributeArgument(); // UserData["AST"]?
    aa.Value = emit_expression(p.expr);
    aa.Name = p.id.str;
    return aa;
}

private static CodeTypeReference emit_pointer_type(pointer_type p) {
    throw new Unsupported("unhandled pointer type");
} // emit_pointer_type

private static CodeTypeReference emit_void_pointer_type(void_pointer_type p) {
    throw new Unsupported("unhandled void pointer type");
} // emit_void_pointer_type

private static CodeExpression emit_sizeof_expression(sizeof_expression p) {
    throw new Unsupported("unhandled sizeof expression");
} // emit_sizeof_expression

private static CodeStatement emit_fixed_statement(fixed_statement p) {
    throw new Unsupported("unhandled fixed statement");
} // emit_fixed_statement

private static string emit_fixed_declarator(fixed_declarator p) {
    throw new Unsupported("unhandled fixed declarator");
} // emit_fixed_declarator

private static CodeExpression emit_stackalloc_initializer(stackalloc_initializer p) {
    throw new Unsupported("unhandled stackalloc initializer");
} // emit_stackalloc_initializer

private static CodeExpression emit_variable_initializer(variable_initializer p) {
    if (p is stackalloc_initializer)
        return emit_stackalloc_initializer((stackalloc_initializer) p);
    if (p is expr_initializer)
        return emit_expr_initializer((expr_initializer) p);
    if (p is array_initializer)
        throw new Unsupported("should be handled elsewhere");
        //return emit_array_initializer((array_initializer) p);
    throw new Unsupported(p.ToString());
} // emit_variable_initializer

private static CodeExpression emit_expr_initializer(expr_initializer p) {
    return emit_expression(p.expr);
} // emit_expr_initializer

private static void emit_array_initializer(array_initializer p, CodeExpressionCollection ec) {
    foreach (variable_initializer k in p.a) {
        CodeExpression s = emit_variable_initializer(k);
        ec.Add(s);
    }
} // emit_array_initializer

} // class AST2CodeDom
