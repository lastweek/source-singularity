using System;
using System.IO;
using System.Text;
using System.Collections;
using System.Diagnostics;

public class typecheck {
    protected MessageWriter msg;
    protected BuiltinTypes T;
    protected TextWriter w;
    public typecheck(TextWriter w, MessageWriter msg) {
        this.w = w;
        this.msg = msg;
    }
    public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            (new typecheck(w, msg)).compilation(ast);
        return ast;
    }

    public ClassType currentClass = null;

    public virtual void accessor_declaration(accessor_declaration ast, type ty) {
        attribute_sections(ast.sym, ast.attrs);
        if (ast.body != null)
            statement(ast.body);
    }
    public static void addMethod(string name, MethodList methods, params Type[] types) {
        Signature[] sigs = signatures(types.Length - 1, types);
        foreach (Method m in methods)
            if (m.signature.Equals(sigs[0]))
                return;
        methods.Add(predefined(name, sigs)[0]);
    }
    public virtual void alias_directive(alias_directive ast) {
        dotted_name(ast.name);
    }
    public virtual void arglist_parameter(arglist_parameter ast, SymbolTable bindings) {
        attribute_sections(bindings[ast.arglist.str], ast.attrs);
    }
    public static string argListToString(argumentList args) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < args.Count; i++) {
            if (i > 0)
                sb.Append(',');
            sb.Append(args[i].expr.typ.FullName);
        }
        return sb.ToString();
    }
    public virtual bool argMatch(argument arg, InputElement formalModifier, Type formalType) {
        if (formalModifier != null && arg.kind != null
        && formalModifier.str == arg.kind.str && arg.expr.typ.Equals(formalType))
            return true;
        if (implicitCvt(arg.expr, formalType) && formalModifier == arg.kind)
            return true;
        return false;
    }
    public virtual void argument(argument ast) {
        ast.typ = expression(ast.expr);
        if (ast.kind != null && !is_variable(ast.expr))
              msg.Error(ast.expr.begin, "{0} argument must be a variable", ast.kind.str);
    }
    public static argumentList actuals(params expression[] exprs) {
        argumentList args = new argumentList();
        foreach (expression e in exprs)
            args.Add(new argument(null, e));
        return args;
    }
    public virtual void array_creation_expression1(array_creation_expression1 ast) {
        Type ty = type(ast.ty);
        if (ty is ArrayType)
            msg.Error(ast.ty.begin, "non-array type required");
        if (ast.ranks.Count > 0)
            ty = new ArrayType(ty, ast.ranks.Count, T.Array);
        ArrayType aty = new ArrayType(ty, ast.exprs.Count, T.Array);
        ast.typ = aty;
        for (int i = 0; i < ast.exprs.Count; i++) {
            expression e = ast.exprs[i];
            expression(e);
            if (e.typ.IsSigned || e.typ.IsUnsigned) {
                Method method = null;
                     if (implicitCvt(e, T.Int, ref method))  e = cast(T.Int,   e, method);
                else if (implicitCvt(e, T.UInt, ref method)) e = cast(T.UInt,  e, method);
                else if (implicitCvt(e, T.Long, ref method)) e = cast(T.Long,  e, method);
                else if (implicitCvt(e, T.ULong, ref method))e = cast(T.ULong, e, method);
                ast.exprs[i] = e;
            } else
                error(e, "integral type", e.typ);
        }
        if (ast.init != null)
            variable_initializer(ast.init, aty);
    }
    public virtual void array_creation_expression2(array_creation_expression2 ast) {
        ast.typ = type(ast.ty);
        if (ast.typ is ArrayType) {
            ArrayType aty = (ArrayType)ast.typ;
            variable_initializer(ast.init, aty);
        } else
            msg.Error(ast.ty.begin, "array type required");
    }
    public virtual void array_initializer(array_initializer ast, ArrayType aty) {
        int rank = array_initializer(ast, aty.elementType);
        if (rank < aty.rank)
            msg.Error(ast.end, "insufficient number of initializers");
        else if (rank > aty.rank)
            msg.Error(ast.end, "too many initializers");
    }
    public virtual int array_initializer(array_initializer ast, Type ty) {
        int rank = 0;
        foreach (variable_initializer x in ast.a)
            if (x is array_initializer)
                rank = array_initializer((array_initializer)x, ty);
            else
                variable_initializer(x, ty);
        return rank + 1;
    }
    public virtual void as_expression(as_expression ast) {
        Type ty = expression(ast.expr);
        ast.typ = type(ast.ty);
        if (!ast.typ.IsReferenceType || !explicitCvt(ast.expr, ast.typ))
            msg.Error(ast.ty.begin, "'{0}' can never be a '{1}'",
                ty.FullName, ast.typ.FullName);
    }
    public virtual expression assign(Type lhsType, string op, expression rhs) {
        Method method = null;
        if (implicitCvt(rhs, lhsType, ref method))
            rhs = cast(lhsType, rhs, method);
        else
            msg.Error(rhs.begin, "a '{0}' cannot be assigned to a '{1}'",
                rhs.typ.FullName, lhsType.FullName);
        return rhs;
    }
    public virtual void assignment_expression(assignment_expression ast) {
        ast.typ = expression(ast.e1, "=", ref ast.e2, ref ast.method);
    }
    public virtual void attribute(attribute ast) {
        ClassType c = (ClassType)type(ast.name);
        if (ast.arguments != null) {
            attribute_arguments(ast.arguments);
            ast.method = (Constructor)invoke(getMethods(c.Name, c), ast.arguments.args, ast);
        } else
            ast.method = (Constructor)invoke(getMethods(c.Name, c), argumentList.New(), ast);
    }
    public virtual void attribute_arguments(attribute_arguments ast) {
        foreach (argument x in ast.args) {
            argument(x);
            if (!is_constant(x.expr.value))
                msg.Error("constant expression required");
        }
        foreach (named_argument x in ast.namedargs)
            named_argument(x);
    }
    public virtual void attribute_section(attribute_section ast) {
        foreach (attribute x in ast.attributes)
            attribute(x);
    }
    public virtual void attribute_sections(attribute_sectionList attrs) {
        foreach (attribute_section x in attrs)
            attribute_section(x);
    }
    public virtual void attribute_sections(Symbol t, attribute_sectionList attrs) {
        attribute_sections(attrs);
        t.AddAttributes(attrs);
    }
    public virtual void base_access(base_access ast) {
        ast.typ = ast.sym;
    }
    public virtual void base_initializer(base_initializer ast, ClassType ty) {
        foreach (argument x in ast.args)
            argument(x);
        ty = ty.baseClass;
        ast.method = (Constructor)invoke(getMethods(ty.Name, ty), ast.args, ast);
    }
    public virtual void binary_declarator(binary_declarator ast) {
        type(ast.ty);
        type(ast.t1);
        type(ast.t2);
    }
    public virtual void binary_expression(binary_expression ast) {
        expression(ast.e1);
        expression(ast.e2);
        ast.method = binaryOp(ast.op, ref ast.e1, ref ast.e2);
        if (ast.method != null)
            ast.typ = ast.method.Type;
        else
            ast.typ = T.Int;
        if (ast.method != null)
            try {
                ast.value = fold(ast.op.str, ast.e1.value, ast.e2.value);
            } catch (ArithmeticException) {
                msg.Error(ast.op, "arithmetic exception in constant expression");
            }
    }
    public virtual Method binaryOp(InputElement op, ref expression e1, ref expression e2) {
        argumentList args = actuals(e1, e2);
        MethodList m = candidates(bind.binaryOpName(op), args, e1.typ, e2.typ);
        if (m == null) {
            if (op.str != "<<" && op.str != ">>"
            && e1.typ.IsNumeric && e1.typ.IsNumeric)
                promote(op, ref e1, ref e2);
            args[0].expr = e1;
            args[1].expr = e2;
            m = binaryOperator(op.str, e1.typ, e2.typ);
        }
        m = resolve(m, args);
        if (m.Count != 1) {
            error(op, m, e1, e2);
            return null;
        }
        ClassType c = m[0].GetType();
        if (c != null && (op.str == "&&" || op.str == "||")
        && (c.members["op_True"] == null || c.members["op_False"] == null))
            msg.Error(op, "type '{0}' must contain definitions for operator true and false",
                c.FullName);
        switch (op.str) {
        case "+":
            if (m[0].Type == T.String && m[0].declSpace == null) {
                Method concat = T.String.FindMethod("Concat", T.Object, T.Object);
                e1 = cast(concat[0].Type, e1);
                e2 = cast(concat[1].Type, e2);
                return concat;
            }
            break;
        }
        return m[0];
    }
    public virtual MethodList binaryOperator(string op, Type t1, Type t2) {
        MethodList m = binaryOperator(op);
        if      (op == "&&") op = "&";
        else if (op == "||") op = "|";
        switch (op) {
        case "+":
            if (t1 is EnumType) {
                addMethod(op, m, t1, t1, ((EnumType)t1).baseType);
                addMethod(op, m, t1, ((EnumType)t1).baseType, t1);
            }
            if (t2 is EnumType) {
                addMethod(op, m, t2, t2, ((EnumType)t2).baseType);
                addMethod(op, m, t2, ((EnumType)t2).baseType, t2);
            }
            if (t1 is DelegateType)
                addMethod(op, m, t1, t1, t1);
            if (t2 is DelegateType)
                addMethod(op, m, t2, t2, t2);
            break;
        case "-":
            if (t1 is EnumType) {
                addMethod(op, m, ((EnumType)t1).baseType, t1, t1);
                addMethod(op, m, t1, t1, ((EnumType)t1).baseType);
            }
            if (t2 is EnumType) {
                addMethod(op, m, ((EnumType)t2).baseType, t2, t2);
                addMethod(op, m, t2, t2, ((EnumType)t2).baseType);
            }
            if (t1 is DelegateType)
                addMethod(op, m, t1, t1, t1);
            if (t2 is DelegateType)
                addMethod(op, m, t2, t2, t2);
            break;
        case "&": case "|": case "^":
            if (t1 is EnumType)
                addMethod(op, m, t1, t1, t1);
            if (t2 is EnumType)
                addMethod(op, m, t2, t2, t2);
            break;
        case "==": case "!=": case "<": case ">": case "<=": case ">=":
            if (t1 is EnumType)
                addMethod(op, m, T.Bool, t1, t1);
            if (t2 is EnumType)
                addMethod(op, m, T.Bool, t2, t2);
            break;
        }
        return m;
    }
    Hashtable _binaryOperators = new Hashtable();
    public virtual MethodList binaryOperator(string op) {
        if (_binaryOperators[op] != null)
            return (MethodList)_binaryOperators[op];
        switch (op) {
        case "+":
            _binaryOperators["+"] = predefined("+", signatures(2,
                T.Int, T.Int, T.Int,
                T.UInt, T.UInt, T.UInt,
                T.Long, T.Long, T.Long,
                T.ULong, T.ULong, T.ULong,
                T.Float, T.Float, T.Float,
                T.Double, T.Double, T.Double,
                T.Decimal, T.Decimal, T.Decimal,
                T.String, T.String, T.String,
                T.String, T.String, T.Object,
                T.String, T.Object, T.String));
            break;
        case "-":
            _binaryOperators["-"] = predefined("-", signatures(2,
                T.Int, T.Int, T.Int,
                T.UInt, T.UInt, T.UInt,
                T.Long, T.Long, T.Long,
                T.ULong, T.ULong, T.ULong,
                T.Float, T.Float, T.Float,
                T.Double, T.Double, T.Double,
                T.Decimal, T.Decimal, T.Decimal));
            break;
        case "*": case "/": case "%": {
            Signature[] sigs = signatures(2,
                T.Int, T.Int, T.Int,
                T.UInt, T.UInt, T.UInt,
                T.Long, T.Long, T.Long,
                T.ULong, T.ULong, T.ULong,
                T.Float, T.Float, T.Float,
                T.Double, T.Double, T.Double,
                T.Decimal, T.Decimal, T.Decimal);
            _binaryOperators["*"] = predefined("*", sigs);
            _binaryOperators["/"] = predefined("/", sigs);
            _binaryOperators["%"] = predefined("%", sigs);
            break; }
        case "<<": case ">>": {
            Signature[] sigs = signatures(2,
                T.Int, T.Int, T.Int,
                T.UInt, T.UInt, T.Int,
                T.Long, T.Long, T.Int,
                T.ULong, T.ULong, T.Int);
            _binaryOperators["<<"] = predefined("<<", sigs);
            _binaryOperators[">>"] = predefined(">>", sigs);
            break; }
        case "<": case "<=": case ">=": case ">": {
            Signature[] sigs = signatures(2,
                T.Bool, T.Int, T.Int,
                T.Bool, T.UInt, T.UInt,
                T.Bool, T.Long, T.Long,
                T.Bool, T.ULong, T.ULong,
                T.Bool, T.Float, T.Float,
                T.Bool, T.Double, T.Double,
                T.Bool, T.Decimal, T.Decimal);
            _binaryOperators["<"] = predefined("<", sigs);
            _binaryOperators["<="] = predefined("<=", sigs);
            _binaryOperators[">="] = predefined(">=", sigs);
            _binaryOperators[">"] = predefined(">", sigs);
            break; }
        case "==": case "!=": {
            Signature[] sigs = signatures(2,
                T.Bool, T.Int, T.Int,
                T.Bool, T.UInt, T.UInt,
                T.Bool, T.Long, T.Long,
                T.Bool, T.ULong, T.ULong,
                T.Bool, T.Float, T.Float,
                T.Bool, T.Double, T.Double,
                T.Bool, T.Decimal, T.Decimal,
                T.Bool, T.Bool, T.Bool,
                T.Bool, T.Object, T.Object,
                T.Bool, T.String, T.String,
                T.Bool, T.Delegate, T.Delegate);
            _binaryOperators["=="] = predefined("==", sigs);
            _binaryOperators["!="] = predefined("!=", sigs);
            break; }
        case "&": case "|": case "^": {
            Signature[] sigs = signatures(2,
                T.Int, T.Int, T.Int,
                T.UInt, T.UInt, T.UInt,
                T.Long, T.Long, T.Long,
                T.ULong, T.ULong, T.ULong,
                T.Bool, T.Bool, T.Bool);
            _binaryOperators["&"]  = predefined("&",  sigs);
            _binaryOperators["|"]  = predefined("|",  sigs);
            _binaryOperators["^"]  = predefined("^",  sigs);
            break; }
        case "&&": case "||": {
            Signature[] sigs = signatures(2,
                T.Bool, T.Bool, T.Bool);
            _binaryOperators["&&"] = predefined("&&", sigs);
            _binaryOperators["||"] = predefined("||", sigs);
            break; }
        default: throw new ArgumentException();
        }
        return (MethodList)_binaryOperators[op];
    }
    public virtual void block_statement(block_statement ast) {
        foreach (statement x in ast.stmts)
            statement(x);
    }
    public virtual expression boolean_expression(expression ast) {
        expression(ast);
        Method method = null;
        if (implicitCvt(ast, T.Bool, ref method))
            ast = cast(T.Bool, ast, method);
        else
            msg.Error(ast.begin, "Boolean expression required");
        ast.typ = T.Bool;
        return ast;
    }
    public virtual void boolean_literal(boolean_literal ast) {
        ast.typ = T.Bool;
        ast.value = ast.token.str == "true";
    }
    public virtual void break_statement(break_statement ast) {
    }
    public virtual MethodList candidates(string opname, argumentList args, Type ty) {
        for (ClassType c = ty as ClassType; c != null; c = c.baseClass) {
            MethodSuite methods = c.members[opname] as MethodSuite;
            if (methods != null) {
                MethodList list = methodMatch(methods.methods, args);
                if (list.Count > 0)
                    return list;
            }
        }
        return null;
    }
    public virtual MethodList candidates(string opname, argumentList args, params Type[] types) {
        MethodList results = null;
        foreach (Type ty in types) {
            MethodList methods = candidates(opname, args, ty);
            if (methods != null && results == null)
                results = new MethodList(methods);
            else if (methods != null && results != null)
                foreach (Method m in methods)
                    if (!results.Contains(m))
                        results.Add(m);
        }
        return results;
    }
    public virtual expression cast(Type t, expression ast, Method m) {
        if (m != null) {
            ast = cast(m[0].Type, ast);
            invocation_expression e = new invocation_expression(ast, actuals(ast));
            e.method = m;
            e.typ = m.Type;
            return cast(m.Type, e);
        } else
            return cast(t, ast);
    }
    public virtual expression cast(Type t, expression ast) {
        if (ast.typ != t && !(t is ArrayType)) {
            type ty = null;
                 if (t == T.Bool)   ty = new bool_type();
            else if (t == T.SByte)  ty = new sbyte_type();
            else if (t == T.Byte)   ty = new byte_type();
            else if (t == T.Short)  ty = new short_type();
            else if (t == T.UShort) ty = new ushort_type();
            else if (t == T.Int)    ty = new int_type();
            else if (t == T.UInt)   ty = new uint_type();
            else if (t == T.Long)   ty = new long_type();
            else if (t == T.ULong)  ty = new ulong_type();
            else if (t == T.Float)  ty = new float_type();
            else if (t == T.Double) ty = new double_type();
            else if (t == T.Decimal)ty = new decimal_type();
            else if (t == T.Char)   ty = new char_type();
            else if (t == T.String) ty = new string_type();
            else if (t == T.Object) ty = new object_type();
            if (ty != null)
                ty.sym = t;
            object value = ast.value;
            AST parent = ast.parent;
            ast = new implicit_cast_expression(ty, ast);
            ast.typ = t;
            ast.value = value;
            ast.link(parent);
            try {
                ast.value = cast(t, ast.value);
            } catch (ArithmeticException) {
                msg.Error(ast.begin, "arithmetic exception in constant expression");
            }
        }
        return ast;
    }
    public object cast(Type t, object x) {
        if (x == null)
            return null;
        if (t == T.Bool   && x is bool
        ||  t == T.String && x is string)
            return x;
        if (x is sbyte)  return cast(t, (long)(sbyte)x);
        if (x is byte)   return cast(t, (ulong)(byte)x);
        if (x is char)   return cast(t, (ulong)(char)x);
        if (x is short)  return cast(t, (long)(short)x);
        if (x is ushort) return cast(t, (ulong)(ushort)x);
        if (x is int)    return cast(t, (long)(int)x);
        if (x is long)   return cast(t, (long)x);
        if (x is ulong)  return cast(t, (ulong)x);
        if (x is float)  return cast(t, (double)(float)x);
        if (x is double) return cast(t, (double)x);
        if (x is decimal)return cast(t, (decimal)x);
        return null;
    }
    object cast(Type t, ulong x) {
        if (t == T.SByte)  return (sbyte)x;
        if (t == T.Byte)   return (byte)x;
        if (t == T.Short)  return (short)x;
        if (t == T.UShort) return (ushort)x;
        if (t == T.Int)    return (int)x;
        if (t == T.UInt)   return (uint)x;
        if (t == T.Long)   return (long)x;
        if (t == T.ULong)  return (ulong)x;
        if (t == T.Float)  return (float)x;
        if (t == T.Double) return (double)x;
        if (t == T.Decimal)return (decimal)x;
        if (t == T.Char)   return (char)x;
        return null;
    }
    object cast(Type t, long x) {
        if (t == T.SByte)  return (sbyte)x;
        if (t == T.Byte)   return (byte)x;
        if (t == T.Short)  return (short)x;
        if (t == T.UShort) return (ushort)x;
        if (t == T.Int)    return (int)x;
        if (t == T.UInt)   return (uint)x;
        if (t == T.Long)   return (long)x;
        if (t == T.ULong)  return (ulong)x;
        if (t == T.Float)  return (float)x;
        if (t == T.Double) return (double)x;
        if (t == T.Decimal)return (decimal)x;
        if (t == T.Char)   return (char)x;
        return null;
    }
    object cast(Type t, double x) {
        if (t == T.SByte)  return (sbyte)x;
        if (t == T.Byte)   return (byte)x;
        if (t == T.Short)  return (short)x;
        if (t == T.UShort) return (ushort)x;
        if (t == T.Int)    return (int)x;
        if (t == T.UInt)   return (uint)x;
        if (t == T.Long)   return (long)x;
        if (t == T.ULong)  return (ulong)x;
        if (t == T.Float)  return (float)x;
        if (t == T.Double) return (double)x;
        if (t == T.Decimal)return (decimal)x;
        if (t == T.Char)   return (char)x;
        return null;
    }
    object cast(Type t, decimal x) {
        if (t == T.SByte)  return (sbyte)x;
        if (t == T.Byte)   return (byte)x;
        if (t == T.Short)  return (short)x;
        if (t == T.UShort) return (ushort)x;
        if (t == T.Int)    return (int)x;
        if (t == T.UInt)   return (uint)x;
        if (t == T.Long)   return (long)x;
        if (t == T.ULong)  return (ulong)x;
        if (t == T.Float)  return (float)x;
        if (t == T.Double) return (double)x;
        if (t == T.Decimal)return (decimal)x;
        if (t == T.Char)   return (char)x;
        return null;
    }
    public virtual void cast_expression(cast_expression ast) {
        ast.typ = type(ast.ty);
        Type ty = expression(ast.expr);
        Method method = null;
        if (explicitCvt(ast.expr, ast.typ, ref method)) {
            ast.expr = cast(ast.typ, ast.expr, method);
            ast.value = ast.expr.value;
        } else
            msg.Error(ast.ty.begin, "invalid cast from '{0}' to '{1}'",
                ty.FullName, ast.typ.FullName);
    }
    public virtual void catch_clause(catch_clause ast) {
        Type ty = type(ast.ty);
        if (!ty.InheritsFrom(T.Exception))
            msg.Error(ast.id, "exception type expected; found '{0}'", ty.FullName);
        statement(ast.block);
    }
    public virtual void catch_clauses(catch_clauses ast) {
        foreach (catch_clause x in ast.specifics)
            catch_clause(x);
        if (ast.general != null)
            statement(ast.general);
    }
    public virtual void character_literal(character_literal ast) {
        bool errorFlag;
        ast.typ = T.Char;
        ast.value = characterLiteral(ast.token.str, out errorFlag);
        if (errorFlag)
            msg.Error(ast.begin, "malformed character literal {0}", ast.token.str);
    }
    public static char characterLiteral(string token, out bool errorFlag) {
        char c = '\uffff';
        CharEnumerator ce = new String2CharEnumerator(token);
        errorFlag = false;
        if (!ce.MoveNext() || ce.Current != '\'')
            errorFlag = true;
        else if (ce.MoveNext())
            switch (ce.Current) {
            case '\x0027':
            case '\u000d':
            case '\u000a':
            case '\u2028':
            case '\u2029':
                errorFlag = true;
                break;
            case '\\':
                c = escapeChar(out errorFlag, ce);
                if (ce.Current != '\'')
                    errorFlag = true;
                break;
            default:
                c = ce.Current;
                if (!ce.MoveNext() || ce.Current != '\'')
                    errorFlag = true;
                break;
            }
        else
            errorFlag = true;
        return c;
    }
    public virtual void checked_expression(checked_expression ast) {
        ast.typ = expression(ast.expr);
    }
    public virtual void checked_expression(checked_expression ast, string op, ref expression rhs, ref Method method) {
        ast.typ = expression(ast.expr, op, ref rhs, ref method);
    }
    public virtual void checked_statement(checked_statement ast) {
        statement(ast.stmt);
    }
    public virtual void class_declaration(class_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        foreach (type x in ast.bases)
            type(x);
        foreach (declaration x in ast.body)
            declaration(x, ast.sym);
    }
    public virtual void compilation(compilation ast) {
        T = ast.global.Types;
        foreach (compilation_unit x in ast.inputs)
            compilation_unit(x);
    }
    public virtual void compilation_unit(compilation_unit ast) {
        foreach (using_directive x in ast.using_directives)
            using_directive(x);
        attribute_sections(ast.attributes);
        foreach (declaration x in ast.declarations)
            declaration(x);
    }
    public virtual void compound_assignment_expression(compound_assignment_expression ast) {
        if (ast.e1 is expr_access)
            member_access((member_access)ast.e1, expression(((expr_access)ast.e1).expr));
        string op = ast.op.str.TrimEnd('=');
        if ((ast.op.tag == "+=" || ast.op.tag == "-=")
        && (ast.e1 is member_access && ((member_access)ast.e1).sym is Event
        ||  ast.e1 is simple_name   && (  (simple_name)ast.e1).sym is Event)) {
            expression(ast.e1, op, ref ast.e2, ref ast.method);
            if (ast.method != null)
                ast.typ = T.Void;
            else
                ast.typ = ast.e2.typ;
        } else {
            ast.typ = expression(ast.e1);
            Type ty = expression(ast.e2);
            expression e1 = ast.e1;
            ast.opmethod = binaryOp(ast.op.Clone(op), ref e1, ref ast.e2);
            if (ast.opmethod != null && !explicitCvt(ast.e2, ast.typ))
                msg.Error(ast.op, "invalid types '{0}' and '{1}' in {2}= operator",
                    ast.e1.typ.FullName, ast.e2.typ.FullName, ast.op.str);
            expression(ast.e1, op, ref ast.e2, ref ast.method);
        }
    }
    public virtual void cond_expression(cond_expression ast) {
        ast.cond = boolean_expression(ast.cond);
        Type t1 = expression(ast.success);
        Type t2 = expression(ast.failure);
        if (t1.Equals(t2))
            ast.typ = t1;
        else if (implicitCvt(ast.success, t2) && !implicitCvt(ast.failure, t1))
            ast.typ = t2;
        else if (implicitCvt(ast.failure, t1) && !implicitCvt(ast.success, t2))
            ast.typ = t1;
        else {
            msg.Error(ast.begin, "incompatible types '{0}' and '{1}' in conditional expression",
                t1.FullName, t2.FullName);
            ast.typ = t1;
            return;
        }
        ast.success = cast(ast.typ, ast.success);
        ast.failure = cast(ast.typ, ast.failure);
        ast.value = fold("?:", ast.cond.value, ast.success.value, ast.failure.value);
    }
    public virtual void const_declarator(const_declarator ast) {
        AST parent = ast.parent;
        ast.parent = null;
        if (parent == null) {
            ast.sym.value = cast(ast.sym.Type, (object)0);
            msg.Error(ast.expr.begin, "circular definition for constant '{0}'", ast.id.str);
        } else if (constant_expression(ref ast.expr, ast.sym.Type))
            ast.sym.value = ast.expr.value;
        else
            ast.sym.value = null;
        ast.parent = parent;
    }
    public virtual void const_statement(const_statement ast) {
        type(ast.ty);
        foreach (const_declarator x in ast.consts)
            constant_value(x.sym);
    }
    public virtual void constant_declaration(constant_declaration ast) {
        attribute_sections(ast.attrs);
        type(ast.ty);
        foreach (const_declarator x in ast.decls) {
            constant_value(x.sym);
            x.sym.AddAttributes(ast.attrs);
        }
    }
    public virtual bool constant_expression(ref expression ast, Type ty) {
        Type t = expression(ast);
        Method method = null;
        if (implicitCvt(ast, ty, ref method))
            ast = cast(t, ast, method);
        else
            error(ast, ty, t);
        if (is_constant(ast.value))
            return true;
        else
            msg.Error(ast.begin, "constant expression required");
        return false;
    }
    public virtual object constant_value(Constant sym) {
        if (sym.value is const_declarator)
            const_declarator((const_declarator)sym.value);
        return sym.value;
    }
    public virtual void constructor_declaration(constructor_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        formals(ast.decl.f, ast.sym);
        if (ast.decl.init != null)
            constructor_initializer(ast.decl.init, ast.sym.GetType());
        if (ast.block != null)
            statement(ast.block);
    }
    public virtual void constructor_initializer(constructor_initializer ast, ClassType ty) {
             if (ast is base_initializer) base_initializer((base_initializer)ast, ty);
        else if (ast is this_initializer) this_initializer((this_initializer)ast, ty);
        else throw new ArgumentException();
    }
    public virtual bool containsCvt(MethodList methods, Signature sig) {
        foreach (Method m in methods)
            if (sig.ArgCount == 1 &&  m.ArgCount == sig.ArgCount
            && m.Type.Equals(sig.Type) && m[0].Type.Equals(sig[0].Type))
                return true;
        return false;
    }
    public virtual int cvtCompare(Type s, Type t1, Type t2) {
        Method method = null;
        if (t1.Equals(t2))
            return 0;
        if (s.Equals(t1))
            return -1;
        if (s.Equals(t2))
            return +1;
        if ( implicitCvt(t1, t2, ref method) && !implicitCvt(t2, t1, ref method))
            return -1;
        if (!implicitCvt(t1, t2, ref method) &&  implicitCvt(t2, t1, ref method))
            return +1;
        if (t1.IsSigned   && t2.IsUnsigned)
            return -1;
        if (t1.IsUnsigned && t2.IsSigned)
            return +1;
        return 0;
    }
    public virtual void declaration(declaration ast) {
        declaration(ast, currentClass);
    }
    public virtual void declaration(declaration ast, ClassType c) {
        ClassType save = currentClass;
        currentClass = c;
             if (ast is namespace_declaration) namespace_declaration((namespace_declaration)ast);
        else if (ast is constant_declaration) constant_declaration((constant_declaration)ast);
        else if (ast is field_declaration) field_declaration((field_declaration)ast);
        else if (ast is method_declaration) method_declaration((method_declaration)ast);
        else if (ast is property_declaration) property_declaration((property_declaration)ast);
        else if (ast is event_declaration1) event_declaration1((event_declaration1)ast);
        else if (ast is event_declaration2) event_declaration2((event_declaration2)ast);
        else if (ast is indexer_declaration) indexer_declaration((indexer_declaration)ast);
        else if (ast is operator_declaration) operator_declaration((operator_declaration)ast);
        else if (ast is constructor_declaration) constructor_declaration((constructor_declaration)ast);
        else if (ast is destructor_declaration) destructor_declaration((destructor_declaration)ast);
        else if (ast is struct_declaration) struct_declaration((struct_declaration)ast);
        else if (ast is interface_declaration) interface_declaration((interface_declaration)ast);
        else if (ast is interface_method_declaration) interface_method_declaration((interface_method_declaration)ast);
        else if (ast is interface_property_declaration) interface_property_declaration((interface_property_declaration)ast);
        else if (ast is interface_event_declaration) interface_event_declaration((interface_event_declaration)ast);
        else if (ast is interface_indexer_declaration) interface_indexer_declaration((interface_indexer_declaration)ast);
        else if (ast is enum_declaration) enum_declaration((enum_declaration)ast);
        else if (ast is class_declaration) class_declaration((class_declaration)ast);
        else if (ast is delegate_declaration) delegate_declaration((delegate_declaration)ast);
        else throw new ArgumentException();
        currentClass = save;
    }
    public virtual void delegate_creation_expression(new_expression ast) {
        DelegateType d = (DelegateType)ast.typ;
        if (ast.args.Count != 1) {
            msg.Error(ast.begin, "wrong number of arguments in delegate creation expression");
            return;
        }
        expression e = ast.args[0].expr;
        if (e.typ is DelegateType) {
            if (!d.Equals(e.typ))
                error(ast, d, e.typ);
            ast.method = (Constructor)((MethodSuite)d.members[d.id.str]).methods[0];
        } else {
            MethodSuite methods = null;
            if (e is member_access)
                methods = ((member_access)e).sym as MethodSuite;
            else if (e is simple_name)
                methods = ((simple_name)e).sym as MethodSuite;
            if (methods != null) {
                MethodList m = new MethodList();
                foreach (Method x in methods)
                    if (x.Type.Equals(d.invoke.Type)
                    &&  x.signature.Equals(d.invoke.signature))
                        m.Add(x);
                if (m.Count == 1) {
                    ast.method = (Constructor)((MethodSuite)d.members[d.id.str]).methods[0];
                    if (e is member_access)
                        ((member_access)e).sym = m[0];
                    else
                        ((simple_name)e).sym = m[0];
                } else
                    error(ast.begin, m, ast.args);
            } else
                msg.Error(ast.begin, "method or delegate expected");
        }
    }
    public virtual void delegate_declaration(delegate_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        type(ast.ty);
        formals(ast.f, ast.sym.invoke);
    }
    public virtual void destructor_declaration(destructor_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        if (ast.block != null)
            statement(ast.block);
    }
    public virtual void do_statement(do_statement ast) {
        statement(ast.body);
        ast.expr = boolean_expression(ast.expr);
    }
    public virtual void dotted_name(dotted_name ast) {
        if (ast.left != null)
            dotted_name(ast.left);
    }
    public virtual void element_access(element_access ast) {
        Type ty = expression(ast.expr);
        if (ty is ArrayType) {
            foreach (argument x in ast.exprs)
                argument(x);
            ArrayType a = (ArrayType)ty;
            if (a.rank != ast.exprs.Count)
                msg.Error(ast.expr.end, "incorrect number of array subscripts; got {0}, expected {1}",
                    ast.exprs.Count.ToString(), a.rank.ToString());
            for (int i = 0; i < ast.exprs.Count; i++) {
                expression e = ast.exprs[i].expr;
                if (e.typ.IsSigned || e.typ.IsUnsigned) {
                         if (implicitCvt(e, T.Int))  e = cast(T.Int,   e);
                    else if (implicitCvt(e, T.UInt)) e = cast(T.UInt,  e);
                    else if (implicitCvt(e, T.Long)) e = cast(T.Long,  e);
                    else if (implicitCvt(e, T.ULong))e = cast(T.ULong, e);
                    ast.exprs[i].expr = e;
                } else
                    error(e, "integral type", e.typ);
            }
            ast.typ = a.elementType;
        } else if (ty is ClassType)
            indexer_access(ast, (ClassType)ty);
    }
    public virtual void element_access(element_access ast, string op, ref expression rhs, ref Method method) {
        Type ty = expression(ast.expr);
        if (ty is ArrayType) {
            element_access(ast);
            expression(rhs);
            rhs = assign(ast.typ, op, rhs);
        } else if (ty is ClassType)
            indexer_access(ast, (ClassType)ty, op, ref rhs, ref method);
    }
    public virtual void empty_statement(empty_statement ast) {
    }
    public virtual void enum_declaration(enum_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        if (ast.ty != null)
            type(ast.ty);
        foreach (enum_member_declaration x in ast.body)
            enum_member_value(x.sym);
    }
    public virtual void enum_member_declaration(enum_member_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        enum_declaration decl = (enum_declaration)ast.parent;
        ast.parent = null;
        if (decl == null && ast.expr != null) {
            ast.sym.value = 0;
            msg.Error(ast.expr.begin, "circular definition for enum member '{0}'", ast.id.str);
        } else if (ast.expr != null) {
            expression(ast.expr);
            ast.expr = cast(decl.sym.baseType, ast.expr);
            ast.sym.value = integer_constant_expression(ast.expr);
        } else {
            int i = decl.body.IndexOf(ast);
            Debug.Assert(i >= 0);
            if (i == 0)
                ast.sym.value = 0;
            else {
                object lhs = cast(T.Long, enum_member_value(decl.body[i-1].sym));
                ast.sym.value = cast(decl.sym.baseType, fold("+", lhs, (object)1L));
            }
        }
        ast.parent = decl;
    }
    public virtual object enum_member_value(EnumMember sym) {
        if (sym.value is enum_member_declaration)
            enum_member_declaration((enum_member_declaration)sym.value);
        return sym.value;
    }
    public void error(Coordinate src, MethodList methods, string details) {
        if (methods.Count == 0)
            msg.Error(src, "no applicable methods for {0}", details);
        else if (methods.Count > 1) {
            msg.Error(src, "{0} possible methods for {1}:",
                 methods.Count.ToString(), details);
            foreach (Method m in methods)
                m.WriteLine(msg.Out);
        }
    }
    public void error(Coordinate src, MethodList methods, argumentList args) {
        error(src, methods, argListToString(args));
    }
    public void error(InputElement op, MethodList methods, expression e1) {
        error(op.coord, methods, String.Format("unary operator {0}{1}",
            op.str, e1.typ.FullName));
    }
    public void error(InputElement op, MethodList methods, expression e1, expression e2) {
        error(op.coord, methods, String.Format("binary operator {1} {0} {2}",
            op.str, e1.typ.FullName, e2.typ.FullName));
    }
    public void error(AST ast, string expect, Type found) {
        msg.Error(ast.begin, "{0} expected; found '{1}'", expect, found.FullName);
    }
    public void error(AST ast, Type expect, Type found) {
        error(ast, String.Format("'{0}'", expect.FullName), found);
    }
    public static char escapeChar(out bool errorFlag, CharEnumerator ce) {
        if (ce.Current != '\\') {
            errorFlag = true;
            return '\xffff';
        }
        if (!ce.MoveNext()) {
            errorFlag = true;
            return '\xffff';
        }
        errorFlag = false;
        switch (ce.Current) {
        default:
            errorFlag = true;
            ce.MoveNext();
            return '\xffff';
        case '\'': ce.MoveNext(); return '\'';
        case '\"': ce.MoveNext(); return '\"';
        case '\\': ce.MoveNext(); return '\\';
        case '0':  ce.MoveNext(); return '\0';
        case 'a':  ce.MoveNext(); return '\a';
        case 'b':  ce.MoveNext(); return '\b';
        case 'f':  ce.MoveNext(); return '\f';
        case 'n':  ce.MoveNext(); return '\n';
        case 'r':  ce.MoveNext(); return '\r';
        case 't':  ce.MoveNext(); return '\t';
        case 'v':  ce.MoveNext(); return '\v';
        case 'x':  return hexEscape(out errorFlag, ce);
        case 'u':
        case 'U':
            char t = unicodeEscape(out errorFlag, ce);
            ce.MoveNext();
            return t;
        }
    }
    public virtual void event_access(expression ast, Event e) {
        if (!(e.IsFieldLike && e.GetType() == currentClass && e.IsAny("abstract", "extern") == 0))
            msg.Error(ast.begin, "event '{0}' can appear only as the left operand of += or -=",
                e.FullName);
        ast.typ = e.Type;
    }
    public virtual void event_access(expression ast, Event e, string op, ref expression rhs, ref Method method) {
        if (e.IsFieldLike && e.GetType() == currentClass && e.IsAny("abstract", "extern") == 0) {
            expression(rhs);
            method = null;
        } else {
            if (op != "+" && op != "-")
                msg.Error(ast.begin, "'{0}' can appear only as the left operand of += or -=",
                    e.FullName);
            expression(rhs);
            if (op == "+")
                method = e.Add;
            else if (op == "-")
                method = e.Remove;
            if (ast is member_access)
                ((member_access)ast).method = method;
        }
        ast.typ = e.Type;
    }
    public virtual void event_accessor(event_accessor ast) {
        attribute_sections(ast.sym, ast.attrs);
        statement(ast.block);
    }
    public virtual void event_declaration1(event_declaration1 ast) {
        attribute_sections(ast.attrs);
        type(ast.ty);
        foreach (event_declarator x in ast.decls)
            if (x.init != null) {
                variable_initializer(x.init, x.sym.Type);
                x.sym.AddAttributes(ast.attrs);
            }
    }
    public virtual void event_declaration2(event_declaration2 ast) {
        attribute_sections(ast.sym, ast.attrs);
        type(ast.ty);
        member_name(ast.name);
        foreach (event_accessor x in ast.accessors)
            event_accessor(x);
    }
    public virtual void explicit_declarator(explicit_declarator ast) {
        type(ast.ty);
        type(ast.t1);
    }
    public virtual bool explicitCvt(expression e1, Type t2) {
        Method method = null;
        return explicitCvt(e1, t2, ref method);
    }
    public virtual bool explicitCvt(expression e1, Type t2, ref Method method) {
        method = null;
        if (stdExplicitCvt(e1, t2))
            return true;
        return explicitCvt(e1.typ, t2, ref method);
    }
    public virtual bool explicitCvt(Type t1, Type t2, ref Method method) {
        if (stdExplicitCvt(t1, t2))
            return true;
        MethodList methods = null;
        if (t1.IsClass) {
            methods = findCvt("op_Implicit", (ClassType)t1, methods);
            methods = findCvt("op_Explicit", (ClassType)t1, methods);
        }
        if (t2.IsClass) {
            methods = findCvt("op_Implicit", (ClassType)t2, methods);
            methods = findCvt("op_Explicit", (ClassType)t2, methods);
        }
        if (methods != null) {
            for (int i = 0; i < methods.Count; ) {
                Method m = methods[i];
                if (stdExplicitCvt(t1, m[i].Type) && stdExplicitCvt(m.Type, t2))
                    i++;
                else
                    methods.Remove(m);
            }
            if (methods.Count == 1) {
                method = methods[0];
                return true;
            }
        }
        return false;
    }
    public virtual void expr_access(expr_access ast) {
        expression(ast.expr);
        Symbol t = null;
        if (ast.expr is simple_name)
            t = ((simple_name)ast.expr).sym;
        else if (ast.expr is member_access)
            t = ((member_access)ast.expr).sym;
        if (t is NameSpace)
            namespace_access(ast, (NameSpace)t);
        else if (t is Type)
            type_access(ast, (Type)t);
        else    // E.I is a property, field, event, method, or constant
            instance_access(ast, ast.expr.typ);
    }
    public virtual void expr_access(expr_access ast, string op, ref expression rhs, ref Method method) {
        expression(ast.expr);
        Symbol t = null;
        if (ast.expr is simple_name)
            t = ((simple_name)ast.expr).sym;
        else if (ast.expr is member_access)
            t = ((member_access)ast.expr).sym;
        if (t is NameSpace)
            msg.Error(ast.id, "Invalid assignment to '{0}.{1}'", t.FullName, ast.id.str);
        else if (t is Type)
            type_access(ast, (Type)t, op, ref rhs, ref method);
        else    // E.I is a property, field, event, method, or constant
            instance_access(ast, ast.expr.typ, op, ref rhs, ref method);
    }
    public virtual void expr_initializer(expr_initializer ast, Type ty) {
        Type t = expression(ast.expr);
        Method method = null;
        if (implicitCvt(ast.expr, ty, ref method))
            ast.expr = cast(ty, ast.expr, method);
        else
            error(ast.expr, ty, t);
    }
    public virtual Type expression(expression ast) {
        if (ast.typ != null)
            return ast.typ;
             if (ast is simple_name) simple_name((simple_name)ast);
        else if (ast is literal) literal((literal)ast);
        else if (ast is member_access) member_access((member_access)ast);
        else if (ast is invocation_expression) invocation_expression((invocation_expression)ast);
        else if (ast is element_access) element_access((element_access)ast);
        else if (ast is this_access) this_access((this_access)ast);
        else if (ast is base_access) base_access((base_access)ast);
        else if (ast is post_expression) post_expression((post_expression)ast);
        else if (ast is new_expression) new_expression((new_expression)ast);
        else if (ast is array_creation_expression1) array_creation_expression1((array_creation_expression1)ast);
        else if (ast is array_creation_expression2) array_creation_expression2((array_creation_expression2)ast);
        else if (ast is typeof_expression) typeof_expression((typeof_expression)ast);
        else if (ast is checked_expression) checked_expression((checked_expression)ast);
        else if (ast is unchecked_expression) unchecked_expression((unchecked_expression)ast);
        else if (ast is unary_expression) unary_expression((unary_expression)ast);
        else if (ast is pre_expression) pre_expression((pre_expression)ast);
        else if (ast is implicit_cast_expression) implicit_cast_expression((implicit_cast_expression)ast);
        else if (ast is cast_expression) cast_expression((cast_expression)ast);
        else if (ast is binary_expression) binary_expression((binary_expression)ast);
        else if (ast is is_expression) is_expression((is_expression)ast);
        else if (ast is as_expression) as_expression((as_expression)ast);
        else if (ast is cond_expression) cond_expression((cond_expression)ast);
        else if (ast is assignment_expression) assignment_expression((assignment_expression)ast);
        else if (ast is compound_assignment_expression) compound_assignment_expression((compound_assignment_expression)ast);
        else if (ast is sizeof_expression) sizeof_expression((sizeof_expression)ast);
        else throw new ArgumentException();
        return ast.typ;
    }
    public virtual Type expression(expression ast, string op, ref expression rhs, ref Method method) {
        Debug.Assert(rhs != null);
             if (ast is simple_name) simple_name((simple_name)ast, op, ref rhs, ref method);
        else if (ast is member_access) member_access((member_access)ast, op, ref rhs, ref method);
        else if (ast is element_access) element_access((element_access)ast, op, ref rhs, ref method);
        else if (ast is checked_expression) checked_expression((checked_expression)ast, op, ref rhs, ref method);
        else if (ast is unchecked_expression) unchecked_expression((unchecked_expression)ast, op, ref rhs, ref method);
        else {
            msg.Error(ast.begin, "Invalid assignment");
            ast.typ = T.Int;
        }
        return ast.typ;
    }
    public virtual void expression_statement(expression_statement ast) {
        expression(ast.expr);
    }
    public virtual void field_declaration(field_declaration ast) {
        attribute_sections(ast.attrs);
        type(ast.ty);
        foreach (field_declarator x in ast.decls) {
            if (x.init != null)
                variable_initializer(x.init, x.sym.Type);
            x.sym.AddAttributes(ast.attrs);
        }
    }
    public virtual void field_access(expression ast, Field f) {
        ast.typ = f.Type;
    }
    public virtual void field_access(expression ast, Field f, string op, ref expression rhs) {
        expression(rhs);
        assign(f.Type, op, rhs);
        ast.typ = f.Type;
    }
    public virtual MethodList findCvt(string op, ClassType ty, MethodList methods) {
        for (ClassType c = ty; c != null; c = c.baseClass) {
            MethodSuite t = c.members[op] as MethodSuite;
            if (t != null) {
                if (methods == null)
                    methods = new MethodList();
                foreach (Method m in t.methods)
                    if (!containsCvt(methods, m.signature))
                        methods.Add(m);
            }
        }
        return methods;
    }
    public virtual void fixed_parameter(fixed_parameter ast, SymbolTable bindings) {
        attribute_sections(bindings[ast.id.str], ast.attrs);
        type(ast.ty);
    }
    public virtual void fixed_statement(fixed_statement ast) {
        type(ast.ty);
        foreach (fixed_declarator x in ast.declarators)
            expression(x.expr);
        statement(ast.body);
    }
    public static object fold(string op, object x) {
        switch (op) {
        case "+":
            if (x is int)    return +(int)x;
            if (x is long)   return +(long)x;
            if (x is float)  return +(float)x;
            if (x is double) return +(double)x;
            if (x is decimal)return +(decimal)x;
            return null;
        case "-":
            if (x is int)    return -(int)x;
            if (x is long)   return -(long)x;
            if (x is float)  return -(float)x;
            if (x is double) return -(double)x;
            if (x is decimal)return -(decimal)x;
            return null;
        case "~":
            if (x is int)   return ~(int)x;
            if (x is uint)  return ~(uint)x;
            if (x is long)  return ~(long)x;
            if (x is ulong) return ~(ulong)x;
            return null;
        case "!":
            if (x is bool)  return !(bool)x;
            return null;
        default: throw new ArgumentException();
        }
    }
    public static object fold(string op, object x, object y) {
        switch (op) {
        case "+":
            if (x is int     && y is int)    return (int)x + (int)y;
            if (x is uint    && y is uint)   return (uint)x + (uint)y;
            if (x is long    && y is long)   return (long)x + (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x + (ulong)y;
            if (x is float   && y is float)  return (float)x + (float)y;
            if (x is double  && y is double) return (double)x + (double)y;
            if (x is decimal && y is decimal)return (decimal)x + (decimal)y;
            if (x is string  && y is string) return (string)x + (string)y;
            return null;
        case "-":
            if (x is int     && y is int)    return (int)x - (int)y;
            if (x is uint    && y is uint)   return (uint)x - (uint)y;
            if (x is long    && y is long)   return (long)x - (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x - (ulong)y;
            if (x is float   && y is float)  return (float)x - (float)y;
            if (x is double  && y is double) return (double)x - (double)y;
            if (x is decimal && y is decimal)return (decimal)x - (decimal)y;
            return null;
        case "*":
            if (x is int     && y is int)    return (int)x * (int)y;
            if (x is uint    && y is uint)   return (uint)x * (uint)y;
            if (x is long    && y is long)   return (long)x * (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x * (ulong)y;
            if (x is float   && y is float)  return (float)x * (float)y;
            if (x is double  && y is double) return (double)x * (double)y;
            if (x is decimal && y is decimal)return (decimal)x * (decimal)y;
            return null;
        case "/":
            if (x is int     && y is int)    return (int)x / (int)y;
            if (x is uint    && y is uint)   return (uint)x / (uint)y;
            if (x is long    && y is long)   return (long)x / (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x / (ulong)y;
            if (x is float   && y is float)  return (float)x / (float)y;
            if (x is double  && y is double) return (double)x / (double)y;
            if (x is decimal && y is decimal)return (decimal)x / (decimal)y;
            return null;
        case "%":
            if (x is int     && y is int)    return (int)x % (int)y;
            if (x is uint    && y is uint)   return (uint)x % (uint)y;
            if (x is long    && y is long)   return (long)x % (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x % (ulong)y;
            if (x is float   && y is float)  return (float)x % (float)y;
            if (x is double  && y is double) return (double)x % (double)y;
            if (x is decimal && y is decimal)return (decimal)x % (decimal)y;
            return null;
        case "<<":
            if (x is int     && y is int)    return (int)x << (int)y;
            if (x is uint    && y is int)    return (uint)x << (int)y;
            if (x is long    && y is int)    return (long)x << (int)y;
            if (x is ulong   && y is int)    return (ulong)x << (int)y;
            return null;
        case ">>":
            if (x is int     && y is int)    return (int)x >> (int)y;
            if (x is uint    && y is int)    return (uint)x >> (int)y;
            if (x is long    && y is int)    return (long)x >> (int)y;
            if (x is ulong   && y is int)    return (ulong)x >> (int)y;
            return null;
        case "&":
            if (x is int     && y is int)    return (int)x & (int)y;
            if (x is uint    && y is uint)   return (uint)x & (uint)y;
            if (x is long    && y is long)   return (long)x & (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x & (ulong)y;
            if (x is bool    && y is bool)   return (bool)x & (bool)y;
            return null;
        case "|":
            if (x is int     && y is int)    return (int)x | (int)y;
            if (x is uint    && y is uint)   return (uint)x | (uint)y;
            if (x is long    && y is long)   return (long)x | (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x | (ulong)y;
            if (x is bool    && y is bool)   return (bool)x | (bool)y;
            return null;
        case "^":
            if (x is int     && y is int)    return (int)x ^ (int)y;
            if (x is uint    && y is uint)   return (uint)x ^ (uint)y;
            if (x is long    && y is long)   return (long)x ^ (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x ^ (ulong)y;
            if (x is bool    && y is bool)   return (bool)x ^ (bool)y;
            return null;
        case "&&":
            if (x is bool    && y is bool)   return (bool)x && (bool)y;
            return null;
        case "||":
            if (x is bool    && y is bool)   return (bool)x || (bool)y;
            return null;
        case "==":
            if (x is int     && y is int)    return (int)x == (int)y;
            if (x is uint    && y is uint)   return (uint)x == (uint)y;
            if (x is long    && y is long)   return (long)x == (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x == (ulong)y;
            if (x is float   && y is float)  return (float)x == (float)y;
            if (x is double  && y is double) return (double)x == (double)y;
            if (x is decimal && y is decimal)return (decimal)x == (decimal)y;
            if (x is bool    && y is bool)   return (bool)x == (bool)y;
            if (x is string  && y is string) return (string)x == (string)y;
            return null;
        case "!=":
            if (x is int     && y is int)    return (int)x == (int)y;
            if (x is uint    && y is uint)   return (uint)x == (uint)y;
            if (x is long    && y is long)   return (long)x == (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x == (ulong)y;
            if (x is float   && y is float)  return (float)x == (float)y;
            if (x is double  && y is double) return (double)x == (double)y;
            if (x is decimal && y is decimal)return (decimal)x == (decimal)y;
            if (x is bool    && y is bool)   return (bool)x == (bool)y;
            if (x is string  && y is string) return (string)x == (string)y;
            return null;
        case "<":
            if (x is int     && y is int)    return (int)x < (int)y;
            if (x is uint    && y is uint)   return (uint)x < (uint)y;
            if (x is long    && y is long)   return (long)x < (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x < (ulong)y;
            if (x is float   && y is float)  return (float)x < (float)y;
            if (x is double  && y is double) return (double)x < (double)y;
            if (x is decimal && y is decimal)return (decimal)x < (decimal)y;
            if (x is string  && y is string) return String.Compare((string)x, (string)y) < 0;
            return null;
        case ">":
            if (x is int     && y is int)    return (int)x > (int)y;
            if (x is uint    && y is uint)   return (uint)x > (uint)y;
            if (x is long    && y is long)   return (long)x > (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x > (ulong)y;
            if (x is float   && y is float)  return (float)x > (float)y;
            if (x is double  && y is double) return (double)x > (double)y;
            if (x is decimal && y is decimal)return (decimal)x > (decimal)y;
            if (x is string  && y is string) return String.Compare((string)x, (string)y) > 0;
            return null;
        case "<=":
            if (x is int     && y is int)    return (int)x <= (int)y;
            if (x is uint    && y is uint)   return (uint)x <= (uint)y;
            if (x is long    && y is long)   return (long)x <= (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x <= (ulong)y;
            if (x is float   && y is float)  return (float)x <= (float)y;
            if (x is double  && y is double) return (double)x <= (double)y;
            if (x is decimal && y is decimal)return (decimal)x <= (decimal)y;
            if (x is string  && y is string) return String.Compare((string)x, (string)y) <= 0;
            return null;
        case ">=":
            if (x is int     && y is int)    return (int)x >= (int)y;
            if (x is uint    && y is uint)   return (uint)x >= (uint)y;
            if (x is long    && y is long)   return (long)x >= (long)y;
            if (x is ulong   && y is ulong)  return (ulong)x >= (ulong)y;
            if (x is float   && y is float)  return (float)x >= (float)y;
            if (x is double  && y is double) return (double)x >= (double)y;
            if (x is decimal && y is decimal)return (decimal)x >= (decimal)y;
            if (x is string  && y is string) return String.Compare((string)x, (string)y) >= 0;
            return null;
        default: throw new ArgumentException();
        }
    }
    public static object fold(string op, object x, object y, object z) {
        switch (op) {
        case "?:":
            if (x is bool && y != null && z != null) return (bool)x ? y : z;
            return null;
        default: throw new ArgumentException();
        }
    }
    public virtual void for_decl(for_decl ast) {
        local_statement(ast.decl);
    }
    public virtual void for_init(for_init ast) {
             if (ast is for_decl) for_decl((for_decl)ast);
        else if (ast is for_list) for_list((for_list)ast);
        else throw new ArgumentException();
    }
    public virtual void for_list(for_list ast) {
        foreach (expression x in ast.exprs)
            expression(x);
    }
    public virtual void for_statement(for_statement ast) {
        if (ast.init != null)
            for_init(ast.init);
        if (ast.cond != null)
            ast.cond = boolean_expression(ast.cond);
        foreach (expression x in ast.iterators)
            expression(x);
        statement(ast.body);
    }
    public virtual void foreach_statement(foreach_statement ast) {
        Type t = type(ast.ty);
        Type ty = expression(ast.expr);
        statement(ast.body);
        if (!(ty is ClassType) && !(ty is ArrayType) && !ty.Implements(T.IEnumerable)) {
            msg.Error(ast.expr.begin, "'{0}' is not a collection type", ty.FullName);
            return;
        }
        MethodSuite methods;
        if (ty is ArrayType)
            methods = getMethods("GetEnumerator", T.Array);
        else
            methods = getMethods("GetEnumerator", (ClassType)ty);
        ClassType rty = null;
        if (methods != null)
            foreach (Method m in methods.methods)
                if (m.IsPublic && m.IsInstance && m.Type is ClassType && m.ArgCount == 0) {
                    rty = (ClassType)m.Type;
                    ast.GetEnumerator = m;
                    break;
                }
        if (rty == null && ty.Implements(T.IEnumerable)) {
            methods = getMethods("System.Collections.IEnumerable.GetEnumerator", (ClassType)ty);
            if (methods != null)
                foreach (Method m in methods.methods)
                    if (m.IsInstance && m.Type is ClassType && m.ArgCount == 0) {
                        rty = (ClassType)m.Type;
                        ast.GetEnumerator = m;
                        name_type n = new name_type(new dotted_name(null, new InputElement("System.Collections.IEnumerable")));
                        n.name.sym = T.IEnumerable;
                        n.sym = T.IEnumerable;
                        ast.expr = new implicit_cast_expression(n, ast.expr);
                        break;
                    }
        }
        if (rty == null) {
            msg.Error(ast.expr.begin, "'{0}' does not implement public GetEnumerator() or System.Collections.IEnumerable.GetEnumerator()", ty.FullName);
            return;
        }
        methods = getMethods("MoveNext", rty);
        if (methods == null) {
            msg.Error(ast.expr.begin, "'{0}' does not implement public bool MoveNext()", rty.FullName);
            return;
        }
        bool found = false;
        foreach (Method m in methods.methods)
            if (m.IsPublic && m.IsInstance && m.Type == T.Bool && m.ArgCount == 0) {
                found = true;
                ast.MoveNext = m;
                break;
            }
        if (!found) {
            msg.Error(ast.expr.begin, "'{0}' does not implement public bool MoveNext()", rty.FullName);
            return;
        }
        Method method = null;
        Property p = rty.Lookup("Current", msg) as Property;
        if (p == null || !(p.IsPublic && p.IsInstance && explicitCvt(p.Type, t, ref method)))
            msg.Error(ast.expr.begin, "'{0}' does not implement public {1} Current",
                rty.FullName, t.FullName);
        else
            ast.Current = p;
    }
    public virtual void formals(formals ast, Method m) {
        foreach (parameter x in ast.fixeds)
            parameter(x, m.locals);
        if (ast.param != null)
            parameter(ast.param, m.locals);
    }
    public static Type getFormalType(Method m, int index, Type actual) {
        if (index >= m.ArgCount - 1 && m.IsParams
        && m[m.ArgCount-1].Type is ArrayType && !(actual is ArrayType))
            return ((ArrayType)m[m.ArgCount-1].Type).elementType;
        return m[index].Type;
    }
    public virtual MethodSuite getMethods(string name, ClassType c) {
        MethodSuite m;
        if (name == c.Name) {   // constructor
            m = c.members[name] as MethodSuite;
            for (int i = 0; i < m.Count; i++)
                if (m.methods[i].IsStatic)
                    m.methods.RemoveAt(i--);
        } else
            m = c.Lookup(new InputElement(name), msg) as MethodSuite;
        if (m == null)
            return null;
        for (int i = 0; i < m.Count; i++)
            if (!m.methods[i].IsAccessible(currentClass))
                m.methods.RemoveAt(i--);
        if (m.methods.Count > 0)
            return m;
        return null;
    }
    public virtual void goto_case_statement(goto_case_statement ast) {
        switch_statement s = ast.stmt as switch_statement;
        if (s != null) {
            if (constant_expression(ref ast.expr, s.typ)) {
                if (s.typ != T.Long && s.typ != T.ULong && s.typ != T.String)
                    ast.expr.value = cast(T.UInt, ast.expr.value);
                foreach (switch_expression x in s.values)
                    if ((bool)fold("==", x.expr.value, ast.expr.value)) {
                        ast.label = x;
                        return;
                    }
            }
            msg.Error(ast.begin, "no such target case label");
        } else
            msg.Error(ast.begin, "goto case outside of a switch statement");
    }
    public virtual void goto_default_statement(goto_default_statement ast) {
        switch_statement s = ast.stmt as switch_statement;
        if (s != null) {
            foreach (switch_section x in s.sections)
                foreach (switch_label y in x.labels)
                    if (y is switch_default)
                        return;
            msg.Error(ast.begin, "goto default inside a switch statement with no default case");
        } else
            msg.Error(ast.begin, "goto default outside of a switch statement");
    }
    public virtual void goto_statement(goto_statement ast) {
    }
    public static char hexEscape(out bool errorFlag, CharEnumerator ce) {
        if (ce.Current != 'x') {
            errorFlag = true;
            return '\uffff';
        }
        int count, acc = 0;
        for (count = 0; ce.MoveNext() && count < 4; count++) {
            char c = Char.ToLower(ce.Current);
            if (Char.IsDigit(c))
                acc = (acc<<4) + c - '0';
            else if (c >= 'a' && c <= 'f')
                acc = (acc << 4) + ce.Current - 'a' + 10;
            else {
                errorFlag = true;
                return '\uffff';
            }
        }
        if (count > 0) {
            errorFlag = false;
            return (char)acc;
        }
        errorFlag = true;
        return '\uffff';
    }
    public virtual void if_statement(if_statement ast) {
        ast.expr = boolean_expression(ast.expr);
        statement(ast.thenpart);
        if (ast.elsepart != null)
            statement(ast.elsepart);
    }
    public virtual void implicit_cast_expression(implicit_cast_expression ast) {
        ast.typ = type(ast.ty);
        expression(ast.expr);
    }
    public virtual void implicit_declarator(implicit_declarator ast) {
        type(ast.ty);
        type(ast.t1);
    }
    public virtual bool implicitCvt(expression e1, Type t2) {
        Method method = null;
        return implicitCvt(e1, t2, ref method);
    }
    public virtual bool implicitCvt(expression e1, Type t2, ref Method method) {
        method = null;
        if (stdImplicitCvt(e1, t2))
            return true;
        return implicitCvt(e1.typ, t2, ref method);
    }
    public virtual bool implicitCvt(Type t1, Type t2, ref Method method) {
        if (stdImplicitCvt(t1, t2))
            return true;
        MethodList methods = null;
        if (t1.IsClass)
            methods = findCvt("op_Implicit", (ClassType)t1, methods);
        if (t2.IsClass)
            methods = findCvt("op_Implicit", (ClassType)t2, methods);
        if (methods != null) {
            for (int i = 0; i < methods.Count; ) {
                Method m = methods[i];
                if (stdImplicitCvt(t1, m[i].Type) && stdImplicitCvt(m.Type, t2))
                    i++;
                else
                    methods.Remove(m);
            }
            if (methods.Count == 1) {
                method = methods[0];
                return true;
            }
        }
        return false;
    }
    public virtual void indexer_access(element_access ast, ClassType c) {
        foreach (argument x in ast.exprs)
            argument(x);
        MethodSuite methods =  getMethods(c == T.String ? "get_Chars" : "get_Item", c);
        if (methods == null) {
            msg.Error(ast.end, "no applicable indexer for '{1}[{0}]'", argListToString(ast.exprs), c.FullName);
            ast.typ = T.Int;
        } else {
            ast.get = invoke(methods.methods, ast.exprs, ast);
            ast.typ = ast.get == null ? T.Int : ast.get.Type;
        }
    }
    public virtual void indexer_access(element_access ast, ClassType c, string op, ref expression rhs, ref Method method) {
        foreach (argument x in ast.exprs)
            argument(x);
        expression(rhs);
        MethodSuite methods = getMethods("set_Item", c);
        if (methods == null) {
            msg.Error(ast.end, "no applicable indexer for [{0}]", argListToString(ast.exprs));
            ast.typ = T.Int;
        } else {
            method = invoke(methods.methods, ast.exprs, ast);
            ast.set = method;
            assign(method.locals["value"].Type, "=", rhs);
            ast.typ = rhs.typ;
        }
    }
    public virtual void indexer_declaration(indexer_declaration ast) {
        attribute_sections(ast.attrs);
        type(ast.i.ty);
        if (ast.i.interfacename != null)
            type(ast.i.interfacename);
        foreach (accessor_declaration x in ast.accessors) {
            accessor_declaration(x, ast.i.ty);
            formals(ast.i.f, x.sym);
            x.sym.AddAttributes(ast.attrs);
        }
    }
    public virtual void instance_access(member_access ast, Type ty) {
        Symbol t = member_access(ast, ty);
        if (t is Event && t.IsInstance)
            event_access(ast, (Event)t);
        else if (t is Field && t.IsInstance)
            field_access(ast, (Field)t);
        else if (t is MethodSuite) {
            MethodSuite m = (MethodSuite)t;
            for (int i = 0; i < m.Count; i++)
                if (!m.methods[i].IsInstance)
                    m.methods.RemoveAt(i--);
            if (m.Count == 0)
                msg.Error(ast.id, "Invalid access to '{0}'", t.FullName);
            else {
                ast.sym = m;
                ast.typ = ty;
            }
        } else if (t is Property && t.IsInstance)
            property_access(ast, (Property)t);
        else if (t != null) {
            msg.Error(ast.id, "Invalid access to '{0}'", t.FullName);
            ast.typ = T.Void;
        }
    }
    public virtual void instance_access(member_access ast, Type ty, string op, ref expression rhs, ref Method method) {
        Symbol t = member_access(ast, ty);
        if (t is Event && t.IsInstance)
            event_access(ast, (Event)t, op, ref rhs, ref method);
        else if (t is Field && t.IsInstance)
            field_access(ast, (Field)t, op, ref rhs);
        else if (t is Property && t.IsInstance)
            property_access(ast, (Property)t, op, ref rhs, ref method);
        else if (t != null) {
            msg.Error(ast.id, "Invalid access to '{0}'", t.FullName);
            ast.typ = T.Void;
        }
    }
    public virtual object integer_constant_expression(expression ast) {
        Type ty = expression(ast);
        object value = ast.value;
        if (value is char  || value is long || value is ulong
        ||  value is sbyte || value is byte || value is short
        ||  value is ushort|| value is int  || value is uint)
            return value;
        error(ast, "integral constant expression", ty);
        return 0;
    }
    public virtual void integer_literal(integer_literal ast) {
        string s = ast.token.str.ToLower();
        ulong value = 0;
        bool overflow = false;
        if (s.StartsWith("0x"))
            for (int i = 2; i < s.Length; i++) {
                int d;
                char c = s[i];
                if (Char.IsDigit(c))
                    d = (int)s[i] - '0';
                else if (c >= 'a' && c <= 'f')
                    d = (int)s[i] - 'a' + 10;
                else
                    break;
                if (value > (UInt64.MaxValue - (ulong)d)/16)
                    overflow = true;
                else
                    value = 16*value + (ulong)d;
            }
        else
            for (int i = 0; i < s.Length && Char.IsDigit(s, i); i++) {
                int d = (int)s[i] - '0';
                if (value > (UInt64.MaxValue - (ulong)d)/10)
                    overflow = true;
                else
                    value = 10*value + (ulong)d;
            }
        ast.value = value;
        if (overflow) {
            msg.Error(ast.token, "overflow in integer literal '{0}'", ast.token.str);
            ast.typ = T.ULong;
        } else if (s.EndsWith("ul") || s.EndsWith("lu"))
            ast.typ = T.ULong;
        else if (s.EndsWith("u"))
            if (value <= UInt32.MaxValue) {
                ast.typ = T.UInt;
                ast.value = (uint)value;
            } else
                ast.typ = T.ULong;
        else if (s.EndsWith("l"))
            if (value <= Int64.MaxValue) {
                ast.typ = T.Long;
                ast.value = (long)value;
            } else
                ast.typ = T.ULong;
        else if (value <= Int32.MaxValue) {
            ast.typ = T.Int;
            ast.value = (int)value;
        } else if (value <= UInt32.MaxValue) {
            ast.typ = T.UInt;
            ast.value = (uint)value;
        } else if (value <= Int64.MaxValue) {
            ast.typ = T.Long;
            ast.value = (long)value;
        } else
            ast.typ = T.ULong;
    }
    public virtual void interface_declaration(interface_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        foreach (type x in ast.interfaces)
            type(x);
        foreach (declaration x in ast.body)
            declaration(x, ast.sym);
    }
    public virtual void interface_event_declaration(interface_event_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        type(ast.ty);
    }
    public virtual void interface_indexer_declaration(interface_indexer_declaration ast) {
        attribute_sections(ast.attrs);
        type(ast.ty);
        foreach (accessor_declaration x in ast.accessors) {
            accessor_declaration(x, ast.ty);
            formals(ast.f, x.sym);
            x.sym.AddAttributes(ast.attrs);
        }
    }
    public virtual void interface_method_declaration(interface_method_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        type(ast.ty);
        formals(ast.f, ast.sym);
    }
    public virtual void interface_property_declaration(interface_property_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        type(ast.ty);
        foreach (accessor_declaration x in ast.accessors)
            accessor_declaration(x, ast.ty);
    }
    public virtual void invocation_expression(invocation_expression ast) {
        Type ty = expression(ast.expr);
        foreach (argument x in ast.args)
            argument(x);
        if (ty is DelegateType)
            ast.method = invoke(new MethodList(((DelegateType)ty).invoke), ast.args, ast);
        else if (ast.expr is member_access
             && ((member_access)ast.expr).sym is MethodSuite)
            ast.method = invoke(((member_access)ast.expr).sym as MethodSuite, ast.args, ast);
        else if (ast.expr is simple_name
             && ((simple_name)ast.expr).sym is MethodSuite)
            ast.method = invoke(((simple_name)ast.expr).sym as MethodSuite, ast.args, ast);
        else
            msg.Error(ast.begin, "method or delegate value expected");
        if (ast.method != null)
            ast.typ = ast.method.Type;
        else
            ast.typ = T.Void;
    }
    public virtual Method invoke(MethodSuite methods, argumentList args, AST ast) {
        return invoke(methods == null ? new MethodList() : methods.methods, args, ast);
    }
    public virtual Method invoke(MethodList methods, argumentList args, AST ast) {
        MethodList m = resolve(methods, args);
        if (m.Count != 1)
            error(ast.begin, m, String.Format("({0})", argListToString(args)));
        else {
            for (int i = 0; i < args.Count; i++) {
                Method method = null;
                Type t = getFormalType(m[0], i, args[i].expr.typ);
                if (implicitCvt(args[i].expr, t, ref method))
                    args[i].expr = cast(t, args[i].expr, method);
            }
            return m[0];
        }
        return null;
    }
    public static bool is_constant(object value) {
        return value is char  || value is bool   || value is string
            || value is sbyte || value is byte   || value is short
            || value is ushort|| value is int    || value is uint
            || value is long  || value is ulong  || value is float
            || value is double|| value is decimal;
    }
    public virtual void is_expression(is_expression ast) {
        Type t1 = expression(ast.expr);
        Type t2 = type(ast.ty);
        if (!explicitCvt(ast.expr, t2))
            msg.Warning(ast.ty.begin, "'{0}' is '{1}' cannot be true",
                t1.FullName, t2.FullName);
        ast.typ = T.Bool;
    }
    public static bool is_variable(expression ast) {
        if (ast is simple_name)
            return ((simple_name)ast).sym.IsVariable;
        if (ast is member_access)
            return ((member_access)ast).sym.IsVariable;
        else if (ast is element_access)
            return ((element_access)ast).expr.typ is ArrayType;
        return false;
    }
    public virtual void labeled_statement(labeled_statement ast) {
        statement(ast.stmt);
    }
    public virtual void literal(literal ast) {
             if (ast is integer_literal) integer_literal((integer_literal)ast);
        else if (ast is real_literal) real_literal((real_literal)ast);
        else if (ast is character_literal) character_literal((character_literal)ast);
        else if (ast is string_literal) string_literal((string_literal)ast);
        else if (ast is boolean_literal) boolean_literal((boolean_literal)ast);
        else if (ast is null_literal) null_literal((null_literal)ast);
        else throw new ArgumentException();
    }
    public virtual void local_statement(local_statement ast) {
        type(ast.ty);
        foreach (var_declarator x in ast.vars)
            if (x.init != null)
                variable_initializer(x.init, x.sym.Type);
    }
    public virtual void lock_statement(lock_statement ast) {
        Type ty = expression(ast.expr);
        if (!ty.IsReferenceType)
            error(ast, "reference type", ty);
        statement(ast.body);
    }
    public virtual void member_access(member_access ast) {
             if (ast is expr_access) expr_access((expr_access)ast);
        else if (ast is pointer_access) pointer_access((pointer_access)ast);
        else if (ast is predefined_access) predefined_access((predefined_access)ast);
        else throw new ArgumentException();
    }
    public virtual void member_access(member_access ast, string op, ref expression rhs, ref Method method) {
        if (ast is expr_access)
            expr_access((expr_access)ast, op, ref rhs, ref method);
        else if (ast is pointer_access)
            pointer_access((pointer_access)ast, op, ref rhs);
        else if (ast is predefined_access)
            predefined_access((predefined_access)ast, op, ref rhs, ref method);
        else
            throw new ArgumentException();
    }
    public virtual Symbol member_access(member_access ast, Type ty) {
        Symbol t = ty.Lookup(ast.id, msg);
        if (t == null) {
            msg.Error(ast.id, "Type '{0}' does not contain a member named '{1}'",
                ty.FullName, ast.id.str);
            ast.sym = T.Void;
        } else if (!t.IsAccessible(currentClass)) {
            msg.Error(ast.id, "'{0}' is inaccessible", t.FullName);
            ast.sym = t;
        } else
            ast.sym = t;
        return t;
    }
    public virtual void member_name(member_name ast) {
        if (ast.ty != null)
            type(ast.ty);
    }
    public virtual void method_declaration(method_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        type(ast.ty);
        member_name(ast.name);
        formals(ast.parms, ast.sym);
        if (ast.body != null)
            statement(ast.body);
    }
    public virtual MethodList methodMatch(MethodList methods, argumentList args) {
        MethodList results = new MethodList();
        // collect the applicable normal-form methods
        foreach (Method m in methods)
            if (!m.IsParams && methodMatch(m, args))
                results.Add(m);
        if (results.Count == 0)
            // collect the applicable expanded-form methods
            foreach (Method m in methods)
                if (m.IsParams && methodMatch(m, args))
                    results.Add(m);
        return results;
    }
    public virtual bool methodMatch(Method m, argumentList args) {
        int i;
        if (m.ArgCount == args.Count) { // normal form match
            for (i = 0; i < args.Count; i++)
                if (!argMatch(args[i], m[i].modifier, m[i].Type))
                    break;
            if (i == args.Count)
                return true;
        }
        if (!m.IsParams || args.Count < m.ArgCount - 1)
            return false;   // no possible match or there's an applicable method in normal form
        for (i = 0; i < m.ArgCount - 1; i++)    // expanded-form match
            if (!argMatch(args[i], m[i].modifier, m[i].Type))
                break;
        if (i != m.ArgCount - 1)
            return false;   // failed to match fixed parameters
        Formal last = m[i];
        for ( ; i < args.Count; i++)
            if (!argMatch(args[i], last.modifier, ((ArrayType)last.Type).elementType))
                break;
        return i == args.Count;
    }
    public virtual void named_argument(named_argument ast) {
        expression(ast.expr);
        ast.expr = assign(ast.sym.Type, "=", ast.expr);
    }
    public virtual void namespace_access(member_access ast, NameSpace ns) {
        ast.sym = ns.Lookup(ast.id, msg);
        if (ast.sym == null) {
            msg.Error(ast.id, "Namespace '{0}' does not contain a member named '{1}'",
                ns.FullName, ast.id.str);
            ast.sym = T.Void;
        }
        ast.typ = ast.sym is Type ? (Type)ast.sym : T.Void;
    }
    public virtual void namespace_body(namespace_body ast) {
        foreach (using_directive x in ast.ud)
            using_directive(x);
        foreach (declaration x in ast.declarations)
            declaration(x);
    }
    public virtual void namespace_declaration(namespace_declaration ast) {
        dotted_name(ast.id);
        namespace_body(ast.nb);
    }
    public virtual void namespace_directive(namespace_directive ast) {
        dotted_name(ast.name);
    }
    public virtual void new_expression(new_expression ast) {
        ast.typ = type(ast.ty);
        foreach (argument x in ast.args)
            argument(x);
        if (ast.typ.Is("abstract"))
            msg.Error(ast.ty.begin, "cannot use abstract type '{0}' in new expressions", ast.typ.FullName);
        else if (ast.typ is DelegateType)
            delegate_creation_expression(ast);
        else if (ast.typ.IsValueType && ast.args.Count == 0)
            ast.method = null;
        else if (ast.typ.IsClass) {
            ClassType c = (ClassType)ast.typ;
            ast.method = (Constructor)invoke(getMethods(c.Name, c), ast.args, ast);
        } else
            error(ast.ty, "class, struct, or delegate", ast.typ);
    }
    public virtual void null_literal(null_literal ast) {
        ast.typ = T.Null;
        ast.value = null;
    }
    public virtual void operator_declaration(operator_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        operator_declarator(ast.op);
        if (ast.block != null)
            statement(ast.block);
    }
    public virtual void operator_declarator(operator_declarator ast) {
             if (ast is unary_declarator) unary_declarator((unary_declarator)ast);
        else if (ast is binary_declarator) binary_declarator((binary_declarator)ast);
        else if (ast is implicit_declarator) implicit_declarator((implicit_declarator)ast);
        else if (ast is explicit_declarator) explicit_declarator((explicit_declarator)ast);
        else throw new ArgumentException();
    }
    public virtual void parameter(parameter ast, SymbolTable bindings) {
             if (ast is fixed_parameter) fixed_parameter((fixed_parameter)ast, bindings);
        else if (ast is params_parameter) params_parameter((params_parameter)ast, bindings);
        else if (ast is arglist_parameter) arglist_parameter((arglist_parameter)ast, bindings);
        else throw new ArgumentException();
    }
    public virtual void params_parameter(params_parameter ast, SymbolTable bindings) {
        attribute_sections(bindings[ast.id.str], ast.attrs);
        type(ast.ty);
    }
    public virtual void pointer_access(pointer_access ast) {
        expression(ast.expr);
    }
    public virtual void pointer_access(pointer_access ast, string op, ref expression rhs) {
        expression(ast.expr);
        expression(rhs);
    }
    public virtual void post_expression(post_expression ast) {
        expression(ast.expr);
        ast.method = unaryOp(ast.op, ref ast.expr);
        ast.typ = ast.expr.typ;
        Method method = null;
        expression rhs = ast.expr;
        expression(ast.expr, ast.op.str, ref rhs, ref method);
    }
    public virtual void pre_expression(pre_expression ast) {
        expression(ast.expr);
        ast.method = unaryOp(ast.op, ref ast.expr);
        ast.typ = ast.expr.typ;
        Method method = null;
        expression rhs = ast.expr;
        expression(ast.expr, ast.op.str, ref rhs, ref method);
    }
    public static MethodList predefined(string name, params Signature[] sigs) {
        MethodList results = new MethodList();
        foreach (Signature sig in sigs) {
            Method m = new Method(new InputElement(name), null);
            m.signature = sig;
            results.Add(m);
        }
        return results;
    }
    public virtual void predefined_access(predefined_access ast) {
        type_access(ast, ast.type);
    }
    public virtual void predefined_access(predefined_access ast, string op, ref expression rhs, ref Method method) {
        type_access(ast, ast.type, op, ref rhs, ref method);
    }
    public virtual void promote(InputElement op, ref expression e1) {
        Type t1 = e1.typ;
        if (t1 == T.SByte  || t1 == T.Byte
        ||  t1 == T.UShort || t1 == T.UShort || t1 == T.Char)
            e1 = cast(T.Int, e1);
        else if (op.str == "-" && t1 == T.UInt)
            e1 = cast(T.Long, e1);
    }
    public virtual void promote(InputElement op, ref expression e1, ref expression e2) {
        Type t1 = e1.typ;
        Type t2 = e2.typ;
        if (t1 == T.Decimal || t2 == T.Decimal) {
            if (t1.IsFloating || t2.IsFloating)
                msg.Error(e1.begin, "{0] {1} {2} is an invalid binary expression", t1.FullName, op.str, t2.FullName);
            e1 = cast(T.Decimal, e1);
            e2 = cast(T.Decimal, e2);
        } else if (t1 == T.Double || t2 == T.Double) {
            e1 = cast(T.Double, e1);
            e2 = cast(T.Double, e2);
        } else if (t1 == T.Float || t2 == T.Float) {
            e1 = cast(T.Float, e1);
            e2 = cast(T.Float, e2);
        } else if (t1 == T.ULong || t2 == T.ULong) {
            if (is_constant(e1.value)
            && (t1 == T.Int && (int)e1.value >= 0 || t1 == T.Long && (long)e1.value > 0))
                t1 = T.ULong;
            if (is_constant(e2.value)
            && (t2 == T.Int && (int)e2.value >= 0 || t2 == T.Long && (long)e2.value > 0))
                t2 = T.ULong;
            if (t1.IsSigned || t2.IsSigned)
                msg.Error(e2.begin, "{0} {1} {2} is an invalid binary expression", t1.FullName, op.str, t2.FullName);
            e1 = cast(T.ULong, e1);
            e2 = cast(T.ULong, e2);
        } else if (t1 == T.Long || t2 == T.Long) {
            e1 = cast(T.Long, e1);
            e2 = cast(T.Long, e2);
        } else if (t1 == T.UInt && (t2.IsSigned && t2.Size <= t1.Size)
               ||  t2 == T.UInt && (t1.IsSigned && t1.Size <= t2.Size)) {
            e1 = cast(T.Long, e1);
            e2 = cast(T.Long, e2);
        } else if (t1 == T.UInt) {
            e1 = cast(T.UInt, e1);
            e2 = cast(T.UInt, e2);
        } else if (t1.IsNumeric && t2.IsNumeric) {
            e1 = cast(T.Int, e1);
            e2 = cast(T.Int, e2);
        }
    }
    public virtual void property_access(expression ast, Property p) {
        if (ast is member_access)
            ((member_access)ast).method = p.Get;
        ast.typ = p.Type;
    }
    public virtual void property_access(expression ast, Property p, string op, ref expression rhs, ref Method method) {
        expression(rhs);
        method = p.Set;
        if (ast is member_access)
            ((member_access)ast).method = method;
        ast.typ = p.Type;
    }
    public virtual void property_declaration(property_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        type(ast.ty);
        member_name(ast.name);
        foreach (accessor_declaration x in ast.decls)
            accessor_declaration(x, ast.ty);
    }
    public virtual void real_literal(real_literal ast) {
        string s = ast.token.str.ToLower();
        try {
            switch (s[s.Length-1]) {
            case 'm':
                ast.typ = T.Decimal;
                ast.value = Decimal.Parse(s.Substring(0, s.Length-1));
                break;
            case 'f':
                ast.typ = T.Float;
                ast.value = Single.Parse(s.Substring(0, s.Length-1));
                break;
            case 'd':
                s = s.Substring(0, s.Length-1);
                goto default;
            default:
                ast.typ = T.Double;
                ast.value = Double.Parse(s);
                break;
            }
        } catch (OverflowException) {
            msg.Error(ast.token, "overflow in real literal '{0}'", ast.token.str);
            ast.value = 0.0;
        }
    }
    public virtual MethodList resolve(MethodList methods, argumentList args) {
        // pass1: collect the applicable methods
        MethodList results = methodMatch(methods, args);
        if (results.Count == 1)
            return results;
        // pass 2: find the best method
        Method bestmethod = null;
        foreach (Method m in results)
            if (bestmethod == null)
                bestmethod = m;
            else {
                int bestscore = 0, mscore = 0;
                for (int i = 0; i < args.Count; i++) {
                    int cond = cvtCompare(args[i].expr.typ, getFormalType(bestmethod, i, args[i].expr.typ), getFormalType(m, i, args[i].expr.typ));
                    if (cond < 0)
                        bestscore++;
                    else if (cond > 0)
                        mscore++;
                }
                if (mscore > 0 && bestscore == 0)   // m is better than bestmethod
                    bestmethod = m;
                else if (mscore == 0 && bestscore == 0
                     ||  mscore >  0 && bestscore >  0) // m is just as good as bestmethod
                    bestmethod = null;
                else
                    Debug.Assert(bestscore > 0 && mscore == 0); // bestmethod remains the best
                }
        if (bestmethod == null)
            return results;
        // pass 3: verify best method
        foreach (Method m in results)
            if (m != bestmethod) {
                int bestscore = 0, mscore = 0;
                for (int i = 0; i < args.Count; i++) {
                    int cond = cvtCompare(args[i].expr.typ, getFormalType(bestmethod, i, args[i].expr.typ), getFormalType(m, i, args[i].expr.typ));
                    if (cond < 0)
                        bestscore++;
                    else if (cond > 0)
                        mscore++;
                }
                if (bestscore > 0 && mscore == 0)
                    continue;
                Debug.Fail("Please email this C# program to drh@microsoft.com and toddpro@microsoft.com");
            }
        results.Clear();
        results.Add(bestmethod);
        return results;
    }
    public virtual void resource(resource ast) {
             if (ast is resource_expr) resource_expr((resource_expr)ast);
        else if (ast is resource_decl) resource_decl((resource_decl)ast);
        else throw new ArgumentException();
    }
    public virtual void resource_decl(resource_decl ast) {
        local_statement(ast.local);
        if (!implicitCvt(ast.local.ty.sym, T.IDisposable, ref ast.method))
            error(ast.local.ty, T.IDisposable, ast.local.ty.sym);
        else {
            ast.dispose = ((ClassType)ast.local.ty.sym).FindMethod("Dispose");
            if (ast.dispose == null)
                ast.dispose = ((ClassType)ast.local.ty.sym).FindMethod("IDisposable.Dispose");
        }
    }
    public virtual void resource_expr(resource_expr ast) {
        Method method = null;
        Type ty = expression(ast.expr);
        if (!implicitCvt(ast.expr, T.IDisposable, ref method))
            error(ast.expr, T.IDisposable, ty);
        else {
            ast.expr = cast(ty, ast.expr, method);
            ast.dispose = ((ClassType)ast.expr.typ).FindMethod("Dispose");
            if (ast.dispose == null)
                ast.dispose = ((ClassType)ast.expr.typ).FindMethod("IDisposable.Dispose");
        }
    }
    public virtual void return_statement(return_statement ast) {
        if (ast.expr != null) {
            Type ty = expression(ast.expr);
            if (ast.method.Type != T.Void) {
                Method method = null;
                if (implicitCvt(ast.expr, ast.method.Type, ref method))
                    ast.expr = cast(ast.method.Type, ast.expr, method);
                else
                    error(ast.expr, ast.method.Type, ty);
            }
        }
    }
    public static Signature[] signatures(int arity, params Type[] parms) {
        Signature[] sigs = new Signature[parms.Length/(arity + 1)];
        for (int i = 0, k = 0; i < parms.Length; i += arity + 1, k++) {
            Signature sig = new Signature();
            sig.Type = parms[i];
            for (int n = 1; n <= arity; n++) {
                Formal f = new Formal(new InputElement(String.Format("arg{0}", n)));
                f.Type = parms[i+n];
                sig.Add(f);
            }
            sigs[k] = sig;
        }
        return sigs;
    }
    public virtual void simple_name(simple_name ast) {
        if (ast.sym is Type)
            ast.typ = (Type)ast.sym;
        else if (ast.sym is NameSpace)
            ast.typ = T.Void;
        else if (ast.sym is Event)
            event_access(ast, (Event)ast.sym);
        else if (ast.sym is Field)
            field_access(ast, (Field)ast.sym);
        else if (ast.sym is Property)
            property_access(ast, (Property)ast.sym);
        else if (ast.sym is MethodSuite)
            ast.typ = currentClass;
        else if (ast.sym is Constant) {
            ast.value = constant_value((Constant)ast.sym);
            ast.typ = ast.sym.Type;
            return;
        } else if (ast.sym is EnumMember) {
            ast.value = enum_member_value((EnumMember)ast.sym);
            ast.typ = ast.sym.Type;
            return;
        } else if (ast.sym != null)
            ast.typ = ast.sym.Type;
        else
            ast.typ = T.Void;
        ast.value = null;
    }
    public virtual void simple_name(simple_name ast, string op, ref expression rhs, ref Method method) {
        if (ast.sym is Type || ast.sym is NameSpace)
            msg.Error(ast.begin, "Invalid assignment to '{0}'", ast.sym.FullName);
        else if (ast.sym is Event)
            event_access(ast, (Event)ast.sym, op, ref rhs, ref method);
        else if (ast.sym is Field)
            field_access(ast, (Field)ast.sym, op, ref rhs);
        else if (ast.sym is Property)
            property_access(ast, (Property)ast.sym, op, ref rhs, ref method);
        else if (ast.sym != null) {
            ast.typ = ast.sym.Type;
            expression(rhs);
            rhs = assign(ast.typ, op, rhs);
        }
    }
    public virtual void sizeof_expression(sizeof_expression ast) {
        type(ast.ty);
        ast.typ = T.Int;
    }
    public virtual void stackalloc_initializer(stackalloc_initializer ast, Type ty) {
        type(ast.ty);
        expression(ast.expr);
    }
    public virtual void statement(statement ast) {
             if (ast is expression_statement) expression_statement((expression_statement)ast);
        else if (ast is block_statement) block_statement((block_statement)ast);
        else if (ast is empty_statement) empty_statement((empty_statement)ast);
        else if (ast is labeled_statement) labeled_statement((labeled_statement)ast);
        else if (ast is local_statement) local_statement((local_statement)ast);
        else if (ast is const_statement) const_statement((const_statement)ast);
        else if (ast is if_statement) if_statement((if_statement)ast);
        else if (ast is switch_statement) switch_statement((switch_statement)ast);
        else if (ast is while_statement) while_statement((while_statement)ast);
        else if (ast is do_statement) do_statement((do_statement)ast);
        else if (ast is for_statement) for_statement((for_statement)ast);
        else if (ast is foreach_statement) foreach_statement((foreach_statement)ast);
        else if (ast is break_statement) return;
        else if (ast is continue_statement) return;
        else if (ast is goto_default_statement) goto_default_statement((goto_default_statement)ast);
        else if (ast is goto_statement) goto_statement((goto_statement)ast);
        else if (ast is goto_case_statement) goto_case_statement((goto_case_statement)ast);
        else if (ast is return_statement) return_statement((return_statement)ast);
        else if (ast is throw_statement) throw_statement((throw_statement)ast);
        else if (ast is try_statement) try_statement((try_statement)ast);
        else if (ast is checked_statement) checked_statement((checked_statement)ast);
        else if (ast is unchecked_statement) unchecked_statement((unchecked_statement)ast);
        else if (ast is lock_statement) lock_statement((lock_statement)ast);
        else if (ast is unsafe_statement) statement(((unsafe_statement)ast).block);
        else if (ast is using_statement) using_statement((using_statement)ast);
        else if (ast is fixed_statement) fixed_statement((fixed_statement)ast);
        else throw new ArgumentException();
    }
    public virtual bool stdExplicitCvt(expression e1, Type t2) {
        if (stdImplicitCvt(e1, t2))
            return true;
        return stdExplicitCvt(e1.typ, t2);
    }
    public virtual bool stdExplicitCvt(Type t1, Type t2) {
        if (stdImplicitCvt(t1, t2))
            return true;
        // Explicit numeric conversions
        if (t1.IsNumeric && t2.IsNumeric)
            return true;
        // Explicit enumeration conversions
        if (t1 is EnumType && (t2.IsNumeric || t2 is EnumType)
        ||  t1.IsNumeric   && t2 is EnumType)
            return true;
        // Explicit reference conversions
        if (t1 == T.Object && t2.IsReferenceType
        ||  t2.InheritsFrom(t1)
        ||  t2 is InterfaceType && !t1.Implements(t2)
        ||  t1 is InterfaceType &&  t2.Implements(t1)
        ||  t1 is InterfaceType && t2 is InterfaceType && !t1.InheritsFrom(t2))
            return true;
        ArrayType a1 = t1 as ArrayType, a2 = t2 as ArrayType;
        if (a1 != null && a2 != null && a1.rank == a2.rank
           && a1.elementType.IsReferenceType && a2.elementType.IsReferenceType
           && stdImplicitCvt(a1.elementType, a2.elementType)
        || t1 == T.Array && a2 != null
        || t1 == T.Delegate && t2 is DelegateType)
            return true;
        // Unboxing conversions
        if (t1 == T.Object && t2.IsValueType
        ||  t1 is InterfaceType && t2.IsValueType && t2.Implements(t1))
            return true;
        return false;
    }
    public virtual bool stdImplicitCvt(expression e1, Type t2) {
        Type t1 = e1.typ;
        if (stdImplicitCvt(t1, t2))
            return true;
        // Implicit enumeration conversions
        if (e1 is integer_literal && ((integer_literal)e1).token.str == "0" && t2 is EnumType)
            return true;
        // Implicit constant expression conversions
        if (is_constant(e1.value) && t1 == T.Int) {
            int n = (int)e1.value;
            if (t2 == T.SByte  && n >= System.SByte.MinValue && n <= System.SByte.MaxValue
            ||  t2 == T.Short  && n >= System.Int16.MinValue && n <= System.Int16.MaxValue
            ||  t2 == T.Byte   && n >= 0 && n <= System.Byte.MaxValue
            ||  t2 == T.UShort && n >= 0 && n <= System.UInt16.MaxValue
            || (t2 == T.UInt || t2 == T.ULong) && n >= 0)
                return true;
        }
        if (is_constant(e1.value) && t1 == T.Long && t2 == T.ULong && (long)e1.value >= 0)
            return true;
        return false;
    }
    public virtual bool stdImplicitCvt(Type t1, Type t2) {
        // Identity conversion
        if (t1.Equals(t2))
            return true;
        // Implicit numeric conversions
        if (t1.IsSigned
        && (t2.IsSigned && t2.Size > t1.Size || t2.IsFloating || t2 == T.Decimal))
            return true;
        if (t1.IsUnsigned
        &&((t2.IsSigned || t2.IsUnsigned) && t2.Size > t1.Size || t2.IsFloating || t2 == T.Decimal))
            return true;
        if (t1 == T.Char
        && (t2.IsSigned && t2.Size >  t1.Size || t2.IsUnsigned && t2.Size >= t1.Size || t2.IsFloating || t2 == T.Decimal))
            return true;
        if (t1 == T.Float && t2 == T.Double)
            return true;
        // Implicit reference conversions
        if (t1.IsReferenceType && t2 == T.Object
        ||  t1 == T.Null && t2.IsReferenceType
        ||  t1.InheritsFrom(t2)
        ||  t2 is InterfaceType && t1.Implements(t2))
            return true;
        ArrayType a1 = t1 as ArrayType, a2 = t2 as ArrayType;
        if (a1 != null && a2 != null && a1.rank == a2.rank
           && a1.elementType.IsReferenceType && a1.elementType.IsReferenceType
           && stdImplicitCvt(a1.elementType, a2.elementType)
        || a1 != null && (t2 == T.Array || t2 == T.ICloneable)
        || t1 is DelegateType && (t2 == T.Delegate || t2 == T.ICloneable))
            return true;
        // Boxing conversions
        if (t1.IsValueType && t2 == T.Object
        ||  t1.IsValueType && t2 is InterfaceType && t1.Implements(t2))
            return true;
        return false;
    }
    public virtual void string_literal(string_literal ast) {
        bool errorFlag;
        ast.typ = T.String;
        ast.value = stringLiteral(ast.token.str, out errorFlag);
        if (errorFlag)
            msg.Error(ast.begin, "malformed string literal {0}", ast.token.str);
    }
    public static string stringLiteral(string token, out bool errorFlag) {
        bool done = false;
        StringBuilder sb = new StringBuilder();
        CharEnumerator ce = new String2CharEnumerator(token);
        errorFlag = false;
        if (!ce.MoveNext() || ce.Current != '"')
            errorFlag = true;
        else if (ce.Current == '"')
            ce.MoveNext();
        while (!errorFlag && !done)
            switch (ce.Current) {
            case '\u000d':
            case '\u000a':
            case '\u2028':
            case '\u2029':
                errorFlag = true;
                break;
            case '\\':
                char c = escapeChar(out errorFlag, ce);
                sb.Append(c);
                break;
            case '"':
                if (ce.MoveNext())
                    errorFlag = true;
                else
                    done = true;
                break;
            default:
                sb.Append(ce.Current);
                done = !ce.MoveNext();
                break;
            }
        return sb.ToString();
    }
    public virtual void struct_declaration(struct_declaration ast) {
        attribute_sections(ast.sym, ast.attrs);
        foreach (type x in ast.interfaces)
            type(x);
        foreach (declaration x in ast.body)
            declaration(x, ast.sym);
    }
    public virtual void switch_expression(switch_expression ast, switch_statement sw) {
        Type ty = expression(ast.expr);
        Method method = null;
        if (implicitCvt(ast.expr, sw.typ, ref method))
            ast.expr = cast(sw.typ, ast.expr, method);
        else
            error(ast.expr, sw.typ, ty);
        if (is_constant(ast.expr.value)) {
            int count = sw.values.Count, n = count;
            if (sw.typ != T.Long && sw.typ != T.ULong && sw.typ != T.String)
                ast.expr.value = cast(T.UInt, ast.expr.value);
            sw.values.Add(null);    // ensure a slot
            for ( ; n > 0 && (bool)fold(">=", sw.values[n-1].expr.value, ast.expr.value); n--)
                sw.values[n] = sw.values[n-1];
            if (n < count && (bool)fold("==", sw.values[n].expr.value, ast.expr.value))
                msg.Error(ast.expr.begin, "duplicate case label");
            sw.values[n] = ast;
        } else
            msg.Error(ast.expr.begin, "case label must be a constant");
    }
    public virtual void switch_label(switch_label ast, switch_statement sw) {
             if (ast is switch_expression) switch_expression((switch_expression)ast, sw);
        else if (ast is switch_default) return;
        else throw new ArgumentException();
    }
    public virtual void switch_section(switch_section ast, switch_statement sw) {
        foreach (switch_label x in ast.labels)
            switch_label(x, sw);
    }
    public virtual void switch_section(switch_section ast) {
        foreach (statement s in ast.stmts)
            statement(s);
    }
    public virtual void switch_statement(switch_statement ast) {
        Type ty = expression(ast.expr);
        if (ty.IsNumeric || ty == T.String || ty is EnumType)
            ast.typ = ty;
        else {
            Type sty = null;
            Method method = null;
            foreach (Type t in new Type[] { T. SByte, T.Byte, T.Short, T.UShort,
                     T.Int, T.UInt, T.Long, T.ULong, T.String } )
                if (implicitCvt(ast.expr, t, ref method)) {
                    sty = t;
                    break;
                }
            if (sty == null) {
                msg.Error(ast.expr.begin, "'{0}' is an invalid type for a switch expression",
                    ty.FullName);
                sty = T.Int;
            } else
                ast.expr = cast(sty, ast.expr, method);
            ast.typ = sty;
        }
        ast.values = new switch_expressionList();
        foreach (switch_section x in ast.sections)
            switch_section(x, ast);
        foreach (switch_section x in ast.sections)
            switch_section(x);
    }
    public virtual void this_access(this_access ast) {
        ast.typ = ast.sym;
    }
    public virtual void this_initializer(this_initializer ast, ClassType ty) {
        foreach (argument x in ast.args)
            argument(x);
        ast.method = (Constructor)invoke(getMethods(ty.Name, ty), ast.args, ast);
    }
    public virtual void throw_statement(throw_statement ast) {
        if (ast.expr != null) {
            Type ty = expression(ast.expr);
            if (!ty.InheritsFrom(T.Exception))
                error(ast.expr, T.Exception, ty);
        }
    }
    public virtual void try_statement(try_statement ast) {
        statement(ast.block);
        if (ast.catches != null)
            catch_clauses(ast.catches);
        if (ast.finally_block != null)
            statement(ast.finally_block.block);
    }
    public virtual Type type(type ast) {
        return ast.sym;
    }
    public virtual void type_access(member_access ast, Type ty) {
        Symbol t = member_access(ast, ty);
        if (t is EnumMember) {
            ast.value = enum_member_value((EnumMember)t);
            ast.typ = t.Type;
        } else if (t is Type)
            ast.typ = (Type)t;
        else if (t is Constant) {
            ast.value = constant_value((Constant)t);
            ast.typ = t.Type;
        } else if (t is Event && t.IsStatic)
            event_access(ast, (Event)t);
        else if (t is Field && t.IsStatic)
            field_access(ast, (Field)t);
        else if (t is MethodSuite) {
            MethodSuite m = (MethodSuite)t;
            for (int i = 0; i < m.Count; i++)
                if (!m.methods[i].IsStatic)
                    m.methods.RemoveAt(i--);
            if (m.Count == 0)
                msg.Error(ast.id, "Invalid access to '{0}'", t.FullName);
            else {
                ast.sym = m;
                ast.typ = ty;
            }
        } else if (t is Property && t.IsStatic)
            property_access(ast, (Property)t);
        else if (t != null) {
            msg.Error(ast.id, "Invalid access to '{0}'", t.FullName);
            ast.typ = T.Void;
        }
    }
    public virtual void type_access(member_access ast, Type ty, string op, ref expression rhs, ref Method method) {
        Symbol t = member_access(ast, ty);
        if (t is Event && t.IsStatic)
            event_access(ast, (Event)t, op, ref rhs, ref method);
        else if (t is Field && t.IsStatic)
            field_access(ast, (Field)t, op, ref rhs);
        else if (t is Property && t.IsStatic)
            property_access(ast, (Property)t, op, ref rhs, ref method);
        else if (t != null) {
            msg.Error(ast.id, "Invalid access to '{0}'", t.FullName);
            ast.typ = T.Void;
        }
    }
    public virtual void typeof_expression(typeof_expression ast) {
        type(ast.ty);
        ast.typ = T.Type;
    }
    public virtual void unary_declarator(unary_declarator ast) {
        type(ast.ty);
        type(ast.t1);
    }
    public virtual void unary_expression(unary_expression ast) {
        expression(ast.expr);
        ast.method = unaryOp(ast.op, ref ast.expr);
        ast.typ = T.Int;
        if (ast.method != null)
            ast.typ = ast.method.Type;
        if (ast.method != null && ast.op.str.Length == 1)
            try {
                ast.value = fold(ast.op.str, ast.expr.value);
            } catch (ArithmeticException) {
                msg.Error(ast.op, "arithmetic exception in constant expression");
            }
    }
    public virtual Method unaryOp(InputElement op, ref expression e1) {
        argumentList args = actuals(e1);
        MethodList m = candidates(bind.unaryOpName(op), args, e1.typ);
        if (m == null) {
            promote(op, ref e1);
            args[0].expr = e1;
            m = unaryOperator(op.str, e1.typ);
        }
        m = resolve(m, args);
        if (m.Count != 1)
            error(op, m, e1);
        else
            return m[0];
        return null;
    }
    public virtual MethodList unaryOperator(string op, Type t1) {
        MethodList m = unaryOperator(op);
        switch (op) {
        case "~":
            if (t1 is EnumType)
                addMethod(op, m, t1, t1);
            break;
        }
        return m;
    }
    Hashtable _unaryOperators = new Hashtable();
    public virtual MethodList unaryOperator(string op) {
        if (_unaryOperators[op] != null)
            return (MethodList)_unaryOperators[op];
        switch (op) {
        case "+":
            _unaryOperators["+"] = predefined("+", signatures(1,
                T.Int, T.Int,
                T.UInt, T.UInt,
                T.Long, T.Long,
                T.ULong, T.ULong,
                T.Float, T.Float,
                T.Double, T.Double,
                T.Decimal, T.Decimal));
            break;
        case "-":
            _unaryOperators["-"] = predefined("-", signatures(1,
                T.Int, T.Int,
                T.Long, T.Long,
                T.Float, T.Float,
                T.Double, T.Double,
                T.Decimal, T.Decimal));
            break;
        case "!":
            _unaryOperators["!"] = predefined("!", signatures(1,
                T.Bool, T.Bool));
            break;
        case "~":
            _unaryOperators["~"] = predefined("~", signatures(1,
                T.Int, T.Int,
                T.UInt, T.UInt,
                T.Long, T.Long,
                T.ULong, T.ULong));
            break;
        case "++": case "--": {
            Signature[] sigs = signatures(1,
                T.SByte, T.SByte,
                T.Byte, T.Byte,
                T.Short, T.Short,
                T.UShort, T.UShort,
                T.Int, T.Int,
                T.UInt, T.UInt,
                T.Long, T.Long,
                T.ULong, T.ULong,
                T.Char, T.Char,
                T.Float, T.Float,
                T.Double, T.Double,
                T.Decimal, T.Decimal);
            _unaryOperators["++"] = predefined("++", sigs);
            _unaryOperators["--"] = predefined("--", sigs);
            break; }
        default: throw new ArgumentException();
        }
        return (MethodList)_unaryOperators[op];
    }
    public virtual void unchecked_expression(unchecked_expression ast) {
        ast.typ = expression(ast.expr);
    }
    public virtual void unchecked_expression(unchecked_expression ast, string op, ref expression rhs, ref Method method) {
        ast.typ = expression(ast.expr, op, ref rhs, ref method);
    }
    public virtual void unchecked_statement(unchecked_statement ast) {
        statement(ast.stmt);
    }
    public static char unicodeEscape(out bool errorFlag, CharEnumerator ce) {
        if (ce.Current != 'u' && ce.Current != 'U') {
            errorFlag = true;
            return '\uffff';
        }
        int len;
        if (ce.Current == 'U')
            len = 8;
        else
            len = 4;
        int acc = 0;
        for (int i = 0; i < len; i++) {
            if (!ce.MoveNext()) {
                errorFlag = true;
                return '\uffff';
            }
            char c = Char.ToLower(ce.Current);
            if (Char.IsDigit(c))
                acc = (acc << 4) + ce.Current - '0';
            else if (c >= 'a' && c <= 'f')
                acc = (acc << 4) + ce.Current - 'a';
            else {
                errorFlag = true;
                return '\uffff';
            }
        }
        errorFlag = false;
        return (char)acc;
    }
    public virtual void using_directive(using_directive ast) {
             if (ast is alias_directive) alias_directive((alias_directive)ast);
        else if (ast is namespace_directive) namespace_directive((namespace_directive)ast);
        else throw new ArgumentException();
    }
    public virtual void using_statement(using_statement ast) {
        resource(ast.r);
        statement(ast.body);
    }
    public virtual void variable_initializer(variable_initializer ast, Type ty) {
        ast.typ = ty;
             if (ast is stackalloc_initializer) stackalloc_initializer((stackalloc_initializer)ast, ty);
        else if (ast is expr_initializer) expr_initializer((expr_initializer)ast, ty);
        else if (ast is array_initializer)
            if( ty is ArrayType)
                array_initializer((array_initializer)ast, (ArrayType)ty);
            else
                error(ast, "array type", ty);
        else throw new ArgumentException();
    }
    public virtual void while_statement(while_statement ast) {
        ast.expr = boolean_expression(ast.expr);
        statement(ast.body);
    }
}
