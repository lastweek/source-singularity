using System;
using System.IO;
using System.Compiler;

public class cci {
    public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            return new cci(w, msg).compilation((compilation)ast);
        return null;
    }
    protected Document document;
    protected MessageWriter msg;
    protected TextWriter w;

    public cci(TextWriter w, MessageWriter msg) {
        this.w = w;
        this.msg = msg;
    }

    Node accessor_declaration(accessor_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        if (ast.body != null)
            statement(ast.body);
        // InputElement ast.id
        // [Bind1] Method ast.sym
        // [Emit] MethodBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Node alias_directive(alias_directive ast) {
        // InputElement ast.id
        dotted_name(ast.name);
        // [Bind1] Symbol ast.sym
        return null;
    }
    Expression anonymous_method_expression(anonymous_method_expression ast) {
        foreach (parameter x in ast.formals)
            parameter(x);
        statement(ast.block);
        // Boolean ast.valueUsed
        // [Typecheck] Type ast.typ
        // [MayBeNull,Typecheck] Object ast.value
        return null;
    }
    Parameter arglist_parameter(arglist_parameter ast) {
        Parameter result = new Parameter();
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        return result;
    }
    Expression argument(argument ast) {
        return expression(ast.expr);
    }
    Expression array_creation_expression1(array_creation_expression1 ast) {
        foreach (expression x in ast.exprs)
            expression(x);
        if (ast.init != null)
            array_initializer(ast.init);
        // intList ast.ranks
        type(ast.ty);
        // Boolean ast.valueUsed
        // [Typecheck] Type ast.typ
        // [MayBeNull,Typecheck] Object ast.value
        return null;
    }
    Expression array_creation_expression2(array_creation_expression2 ast) {
        array_initializer(ast.init);
        type(ast.ty);
        // Boolean ast.valueUsed
        // [Typecheck] Type ast.typ
        // [MayBeNull,Typecheck] Object ast.value
        return null;
    }
    Expression array_initializer(array_initializer ast) {
        ConstructArray result = new ConstructArray();
        result.Initializers = new ExpressionList();
        foreach (variable_initializer x in ast.a)
            result.Initializers.Add(variable_initializer(x));
        return result;
    }
    TypeNode array_type(array_type ast) {
        // Int32 ast.rank_specifier
        type(ast.ty);
        // [Bind2] Type ast.sym
        return null;
    }
    Expression as_expression(as_expression ast) {
        return new BinaryExpression(expression(ast.expr),
            new MemberBinding(null, type(ast.ty)), NodeType.As);
    }
    Expression assignment_expression(assignment_expression ast) {
        return new AssignmentExpression(
            new AssignmentStatement(expression(ast.e1), expression(ast.e2)));
    }
    Node attribute(attribute ast) {
        if (ast.arguments != null)
            attribute_arguments(ast.arguments);
        type(ast.name);
        return null;
    }
    Node attribute_arguments(attribute_arguments ast) {
        foreach (expression x in ast.args)
            expression(x);
        foreach (named_argument x in ast.namedargs)
            named_argument(x);
        return null;
    }
    Node attribute_section(attribute_section ast) {
        foreach (attribute x in ast.attributes)
            attribute(x);
        // [MayBeNull] InputElement ast.target
        return null;
    }
    Expression base_access(base_access ast) {
        return new Base();
    }
    Node base_initializer(base_initializer ast) {
        foreach (argument x in ast.args)
            argument(x);
        // [Typecheck] Constructor ast.method
        return null;
    }
    Node binary_declarator(binary_declarator ast) {
        // InputElement ast.id1
        // InputElement ast.id2
        // InputElement ast.op
        type(ast.t1);
        type(ast.t2);
        // [Bind1] Formal ast.sym1
        // [Bind1] Formal ast.sym2
        type(ast.ty);
        // [Bind1] Method ast.method
        return null;
    }
    Expression binary_expression(binary_expression ast) {
        NodeType op;
        switch (ast.op.str) {
        case "+":   op = NodeType.Add; break;
        case "&":   op = NodeType.And; break;
        case "|":   op = NodeType.Or;  break;
        case "^":   op = NodeType.Xor; break;
        case "/":   op = NodeType.Div; break;
        case "=":   op = NodeType.Eq;  break;
        case ">":   op = NodeType.Gt;  break;
        case ">=":  op = NodeType.Ge;  break;
        case "<<":  op = NodeType.Shl; break;
        case "<":   op = NodeType.Lt;  break;
        case "<=":  op = NodeType.Le;  break;
        case "&&":  op = NodeType.LogicalAnd; break;
        case "||":  op = NodeType.LogicalOr; break;
        case "*":   op = NodeType.Mul; break;
        case "!=":  op = NodeType.Ne;  break;
        case "%":   op = NodeType.Rem; break;
        case ">>":  op = NodeType.Shr; break;
        case "-":   op = NodeType.Sub; break;
        default:    op = NodeType.Nop; break;
        }
        return new BinaryExpression(expression(ast.e1), expression(ast.e2), op);
    }
    System.Compiler.Block block(statement ast) {
        if (ast is block_statement)
            return (System.Compiler.Block)statement(ast);
        else
            return new System.Compiler.Block(new StatementList(statement(ast)), context(ast));
    }
    Statement block_statement(block_statement ast) {
        StatementList stmts = new StatementList();
        foreach (statement x in ast.stmts)
            stmts.Add(statement(x));
        return new System.Compiler.Block(stmts, context(ast));
    }
    TypeNode bool_type(bool_type ast) {
        return SystemTypes.Boolean;
    }
    Expression boolean_literal(boolean_literal ast) {
        return new Literal(ast.token.str == "true", SystemTypes.Boolean);
    }
    Statement break_statement(break_statement ast) {
        return new Exit();
    }
    TypeNode byte_type(byte_type ast) {
        return SystemTypes.UInt8;
    }
    Expression cast_expression(cast_expression ast) {
        return new BinaryExpression(expression(ast.expr),
            new MemberBinding(null, typeexpression(ast.ty)), NodeType.Castclass);
    }
    Catch catch_clause(catch_clause ast) {
        Catch result = new Catch();
        result.Type = type(ast.ty);
        if (ast.id != null)
            result.Variable = identifier(ast.id);
        result.Block = block(ast.block);
        return result;
    }
    CatchList catch_clauses(catch_clauses ast) {
        CatchList catches = new CatchList();
        if (ast.general != null)
            catches.Add(new Catch(block(ast.general), null, null));
        foreach (catch_clause x in ast.specifics)
            catches.Add(catch_clause(x));
        return catches;
    }
    TypeNode char_type(char_type ast) {
        return SystemTypes.Char;
    }
    Expression character_literal(character_literal ast) {
        bool errorFlag;
        return new Literal(typecheck.characterLiteral(ast.token.str, out errorFlag), SystemTypes.Char);
    }
    Expression checked_expression(checked_expression ast) {
        BlockExpression result = new BlockExpression();
        result.Block = new System.Compiler.Block(new StatementList(expressionstatement(ast.expr)), true, false);
        return result;
    }
    Statement checked_statement(checked_statement ast) {
        System.Compiler.Block result = block(ast.stmt);
        result.Checked = true;
        result.SuppressCheck = false;
        return result;
    }
    Node class_declaration(class_declaration ast) {
        System.Compiler.Class result = new System.Compiler.Class();
        result.Name = identifier(ast.id);
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        result.Flags = getTypeFlags(stringList(ast.mods), ast.parent is type_declaration);
        foreach (type_parameter x in ast.typeparams)
            type_parameter(x);
        foreach (type x in ast.bases)
            type(x);
        foreach (type_parameter_constraints_clause x in ast.constraints)
            type_parameter_constraints_clause(x);
        result.Members = new MemberList();
        foreach (declaration x in ast.body) {
            Object d = declaration(x);
            if (d is Member)
                result.Members.Add((Member)d);
            else if (d is MemberList) {
                MemberList m = (MemberList)d;
                for (int i = 0; i < m.Length; i++)
                    result.Members.Add(m[i]);
            }
        }
        return result;
    }
    object compilation(compilation ast) {
        Compilation result = new Compilation();
        result.CompilationUnits = new CompilationUnitList();
        foreach (compilation_unit x in ast.inputs)
            result.CompilationUnits.Add(compilation_unit(x));
        return result;
    }
    CompilationUnit compilation_unit(compilation_unit ast) {
        CompilationUnit result = new CompilationUnit();
        result.Nodes = new NodeList();
        document = new Document();
        if (ast.begin.file != null) {
            try {
                StreamReader r = new StreamReader(ast.begin.file);
                document.Text = new DocumentText(r.ReadToEnd());
                r.Close();
            } catch (Exception) {
                document.Text = new DocumentText(source.ToString(ast));
            }
        } else
            document.Text = new DocumentText(source.ToString(ast));
        result.SourceContext = context(ast);
        foreach (attribute_section x in ast.attributes)
            attribute_section(x);
        foreach (using_directive x in ast.using_directives)
            using_directive(x);
        foreach (declaration x in ast.declarations)
            result.Nodes.Add((Node)declaration(x));
        return result;
    }
    Expression compound_assignment_expression(compound_assignment_expression ast) {
        NodeType op;
        switch (ast.op.str) {
        case "+=":  op = NodeType.Add; break;
        case "&=":  op = NodeType.And; break;
        case "|=":  op = NodeType.Or;  break;
        case "^=":  op = NodeType.Xor; break;
        case "/=":  op = NodeType.Div; break;
        case "<<=": op = NodeType.Shl; break;
        case "*=":  op = NodeType.Mul; break;
        case "!=":  op = NodeType.Ne;  break;
        case "%=":  op = NodeType.Rem; break;
        case ">>=": op = NodeType.Shr; break;
        case "-=":  op = NodeType.Sub; break;
        default:    op = NodeType.Nop; break;
        }
        return new AssignmentExpression(
            new AssignmentStatement(expression(ast.e1), expression(ast.e2), op));
    }
    Expression cond_expression(cond_expression ast) {
        return new TernaryExpression(expression(ast.cond),
            expression(ast.success), expression(ast.failure), NodeType.Conditional, null);
    }
    LocalDeclaration const_declarator(const_declarator ast) {
        return new LocalDeclaration(identifier(ast.id), expression(ast.expr));
    }
    Statement const_statement(const_statement ast) {
        LocalDeclarationsStatement result = new LocalDeclarationsStatement();
        result.Constant = true;
        result.Type = type(ast.ty);
        result.Declarations = new LocalDeclarationList();
        foreach (const_declarator x in ast.consts)
            result.Declarations.Add(const_declarator(x));
        return result;
    }
    Node constant_declaration(constant_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        foreach (declarator x in ast.decls)
            declarator(x);
        type(ast.ty);
        // InputElementList ast.mods
        return null;
    }
    TypeNode constructor_constraint(constructor_constraint ast) {
        // [Bind2] Type ast.sym
        return null;
    }
    Node constructor_declaration(constructor_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        if (ast.block != null)
            statement(ast.block);
        constructor_declarator(ast.decl);
        // [Bind1] Constructor ast.sym
        // [Emit] ConstructorBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Node constructor_declarator(constructor_declarator ast) {
        formals(ast.f);
        // InputElement ast.id
        if (ast.init != null)
            constructor_initializer(ast.init);
        return null;
    }
    Node constructor_initializer(constructor_initializer ast) {
             if (ast is base_initializer) return base_initializer((base_initializer)ast);
        else if (ast is this_initializer) return this_initializer((this_initializer)ast);
        else throw new ArgumentException();
    }
    SourceContext context(AST ast) {
        return context(ast.begin, ast.end);
    }
    SourceContext context(Coordinate begin, Coordinate end) {
        Debug.Assert(document != null);
        return new SourceContext(document, begin.line - 1, begin.column - 1 , end.line - 1, end.column - 1);
    }
    Statement continue_statement(continue_statement ast) {
        return new Continue();
    }
    TypeNode decimal_type(decimal_type ast) {
        return SystemTypes.Decimal;
    }
    object declaration(declaration ast) {
        object result = null;
             if (ast is accessor_declaration) result = accessor_declaration((accessor_declaration)ast);
        else if (ast is type_declaration) result = type_declaration((type_declaration)ast);
        else if (ast is constant_declaration) result = constant_declaration((constant_declaration)ast);
        else if (ast is constructor_declaration) result = constructor_declaration((constructor_declaration)ast);
        else if (ast is destructor_declaration) result = destructor_declaration((destructor_declaration)ast);
        else if (ast is event_declaration1) result = event_declaration1((event_declaration1)ast);
        else if (ast is event_declaration2) result = event_declaration2((event_declaration2)ast);
        else if (ast is field_declaration) result = field_declaration((field_declaration)ast);
        else if (ast is interface_method_declaration) result = interface_method_declaration((interface_method_declaration)ast);
        else if (ast is method_declaration) result = method_declaration((method_declaration)ast);
        else if (ast is indexer_declaration) result = indexer_declaration((indexer_declaration)ast);
        else if (ast is interface_event_declaration) result = interface_event_declaration((interface_event_declaration)ast);
        else if (ast is interface_indexer_declaration) result = interface_indexer_declaration((interface_indexer_declaration)ast);
        else if (ast is interface_property_declaration) result = interface_property_declaration((interface_property_declaration)ast);
        else if (ast is namespace_declaration) result = namespace_declaration((namespace_declaration)ast);
        else if (ast is operator_declaration) result = operator_declaration((operator_declaration)ast);
        else if (ast is property_declaration) result = property_declaration((property_declaration)ast);
        else throw new ArgumentException();
        if (result is Member)
            ((Member)result).SourceContext = context(ast);
        return result;
    }
    Node declarator(declarator ast) {
             if (ast is const_declarator) return const_declarator((const_declarator)ast);
        else if (ast is event_declarator) return event_declarator((event_declarator)ast);
        else if (ast is field_declarator) return field_declarator((field_declarator)ast);
        else if (ast is fixed_declarator) return fixed_declarator((fixed_declarator)ast);
        else if (ast is var_declarator) return var_declarator((var_declarator)ast);
        else throw new ArgumentException();
    }
    Node delegate_declaration(delegate_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        foreach (type_parameter x in ast.typeparams)
            type_parameter(x);
        foreach (type_parameter_constraints_clause x in ast.constraints)
            type_parameter_constraints_clause(x);
        formals(ast.f);
        // InputElement ast.id
        type(ast.ty);
        // [Bind1] DelegateType ast.sym
        // [Emit] Type ast.type
        // InputElementList ast.mods
        return null;
    }
    Node destructor_declaration(destructor_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        if (ast.block != null)
            statement(ast.block);
        // InputElement ast.id
        // [Bind1] Method ast.sym
        // [Emit] MethodBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Statement do_statement(do_statement ast) {
        return new DoWhile(expression(ast.expr), block(ast.body));
    }
    Expression dotted_name(dotted_name ast) {
        Expression result;
        if (ast.left != null)
            result = new QualifiedIdentifier(dotted_name(ast.left), identifier(ast.right));
        else
            result = identifier(ast.right);
        if (ast.typeargs != null) {
            foreach (type x in ast.typeargs)
                type(x);
        }
        result.SourceContext = context(ast);
        return result;
    }
    TypeNode double_type(double_type ast) {
        return SystemTypes.Double;
    }
    Expression element_access(element_access ast) {
        ExpressionList args = new ExpressionList();
        foreach (argument x in ast.exprs)
            args.Add(argument(x));
        return new Indexer(expression(ast.expr), args);
    }
    Statement empty_statement(empty_statement ast) {
        return new System.Compiler.Block();
    }
    Node enum_declaration(enum_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        foreach (enum_member_declaration x in ast.body)
            enum_member_declaration(x);
        // InputElement ast.id
        if (ast.ty != null)
            type(ast.ty);
        // [Bind1] EnumType ast.sym
        // [Emit] Type ast.type
        // InputElementList ast.mods
        return null;
    }
    Node enum_member_declaration(enum_member_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        if (ast.expr != null)
            expression(ast.expr);
        // InputElement ast.id
        // [Bind1] EnumMember ast.sym
        // [Emit] FieldBuilder ast.builder
        return null;
    }
    Node event_accessor(event_accessor ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        statement(ast.block);
        // InputElement ast.id
        // [Bind1] Method ast.sym
        // [Emit] MethodBuilder ast.builder
        return null;
    }
    Node event_declaration1(event_declaration1 ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        foreach (declarator x in ast.decls)
            declarator(x);
        type(ast.ty);
        // InputElementList ast.mods
        return null;
    }
    Node event_declaration2(event_declaration2 ast) {
        foreach (event_accessor x in ast.accessors)
            event_accessor(x);
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        member_name(ast.name);
        type(ast.ty);
        // [Bind1] Event ast.sym
        // [Emit] EventBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Node event_declarator(event_declarator ast) {
        if (ast.init != null)
            variable_initializer(ast.init);
        // [Bind1] Event ast.sym
        // [Emit] FieldBuilder ast.builder
        // [Emit] EventBuilder ast.event_builder
        // [Emit] MethodBuilder ast.add_builder
        // [Emit] MethodBuilder ast.remove_builder
        // InputElement ast.id
        return null;
    }
    Node explicit_declarator(explicit_declarator ast) {
        // InputElement ast.id1
        type(ast.t1);
        // [Bind1] Formal ast.sym
        type(ast.ty);
        // [Bind1] Method ast.method
        return null;
    }
    Expression expr_access(expr_access ast) {
        Expression result = new QualifiedIdentifier(expression(ast.expr), identifier(ast.id));
        if (ast.typeargs != null) {
            foreach (type x in ast.typeargs)
                type(x);
        }
        return result;
    }
    Expression expr_initializer(expr_initializer ast) {
        return expression(ast.expr);
    }
    Expression expression(expression ast) {
        Expression result = null;
             if (ast is anonymous_method_expression) result = anonymous_method_expression((anonymous_method_expression)ast);
        else if (ast is array_creation_expression1) result = array_creation_expression1((array_creation_expression1)ast);
        else if (ast is array_creation_expression2) result = array_creation_expression2((array_creation_expression2)ast);
        else if (ast is as_expression) result = as_expression((as_expression)ast);
        else if (ast is assignment_expression) result = assignment_expression((assignment_expression)ast);
        else if (ast is base_access) result = base_access((base_access)ast);
        else if (ast is binary_expression) result = binary_expression((binary_expression)ast);
        else if (ast is literal) result = literal((literal)ast);
        else if (ast is cast_expression) result = cast_expression((cast_expression)ast);
        else if (ast is checked_expression) result = checked_expression((checked_expression)ast);
        else if (ast is compound_assignment_expression) result = compound_assignment_expression((compound_assignment_expression)ast);
        else if (ast is cond_expression) result = cond_expression((cond_expression)ast);
        else if (ast is element_access) result = element_access((element_access)ast);
        else if (ast is member_access) result = member_access((member_access)ast);
        else if (ast is implicit_cast_expression) result = implicit_cast_expression((implicit_cast_expression)ast);
        else if (ast is invocation_expression) result = invocation_expression((invocation_expression)ast);
        else if (ast is is_expression) result = is_expression((is_expression)ast);
        else if (ast is new_expression) result = new_expression((new_expression)ast);
        else if (ast is post_expression) result = post_expression((post_expression)ast);
        else if (ast is pre_expression) result = pre_expression((pre_expression)ast);
        else if (ast is simple_name) result = simple_name((simple_name)ast);
        else if (ast is sizeof_expression) result = sizeof_expression((sizeof_expression)ast);
        else if (ast is this_access) result = this_access((this_access)ast);
        else if (ast is typeof_expression) result = typeof_expression((typeof_expression)ast);
        else if (ast is unary_expression) result = unary_expression((unary_expression)ast);
        else if (ast is unchecked_expression) result = unchecked_expression((unchecked_expression)ast);
        else throw new ArgumentException();
        result.SourceContext = context(ast);
        return result;
    }
    Statement expression_statement(expression_statement ast) {
        return expressionstatement(ast.expr);
    }
    ExpressionStatement expressionstatement(expression ast) {
        return new ExpressionStatement(expression(ast));
    }
    MemberList field_declaration(field_declaration ast) {
        MemberList result = new MemberList();
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        FieldFlags flags = getFieldFlags(stringList(ast.mods));
        foreach (field_declarator x in ast.decls) {
            System.Compiler.Field f = field_declarator(x);
            f.Type = type(ast.ty);
            f.Flags = flags;
            f.SourceContext = context(x);
            result.Add(f);
        }
        return result;
    }
    System.Compiler.Field field_declarator(field_declarator ast) {
        System.Compiler.Field result = new System.Compiler.Field(identifier(ast.id));
        if (ast.init != null)
            result.Initializer = variable_initializer(ast.init);
        return result;
    }
    Finally finally_clause(finally_clause ast) {
        return new Finally(block(ast.block));
    }
    Node fixed_declarator(fixed_declarator ast) {
        expression(ast.expr);
        // [Bind1] Local ast.sym
        // InputElement ast.id
        return null;
    }
    Parameter fixed_parameter(fixed_parameter ast) {
        Parameter result = new Parameter(identifier(ast.id), type(ast.ty));
        if (ast.mod != null)
            result.Flags = ParameterFlags.Out;
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        return result;
    }
    Statement fixed_statement(fixed_statement ast) {
        Fixed result = new Fixed();
        foreach (fixed_declarator x in ast.declarators)
            fixed_declarator(x);
        type(ast.ty);
        result.Body = block(ast.body);
        return result;
    }
    TypeNode float_type(float_type ast) {
        return SystemTypes.Single;
    }
    StatementList for_decl(for_decl ast) {
        return new StatementList(local_statement(ast.decl));
    }
    StatementList for_init(for_init ast) {
             if (ast is for_decl) return for_decl((for_decl)ast);
        else if (ast is for_list) return for_list((for_list)ast);
        else throw new ArgumentException();
    }
    StatementList for_list(for_list ast) {
        StatementList result = new StatementList();
        foreach (expression x in ast.exprs)
            result.Add(expressionstatement(x));
        return result;
    }
    Statement for_statement(for_statement ast) {
        For result = new For();
        if (ast.init != null)
            result.Initializer = for_init(ast.init);
        if (ast.cond != null)
            result.Condition = expression(ast.cond);
        result.Incrementer = new StatementList();
        foreach (expression x in ast.iterators)
            result.Incrementer.Add(expressionstatement(x));
        result.Body = block(ast.body);
        return result;
    }
    Statement foreach_statement(foreach_statement ast) {
        ForEach result = new ForEach();
        result.TargetVariableType = type(ast.ty);
        result.TargetVariable = identifier(ast.id);
        result.SourceEnumerable = expression(ast.expr);
        result.Body = block(ast.body);
        return null;
    }
    ParameterList formals(formals ast) {
        ParameterList result = new ParameterList();
        foreach (parameter x in ast.fixeds)
            result.Add(parameter(x));
        if (ast.param != null)
            parameter(ast.param);
        return result;
    }
    Node generic_interface_method_declaration(generic_interface_method_declaration ast) {
        foreach (type_parameter x in ast.typeparams)
            type_parameter(x);
        foreach (type_parameter_constraints_clause x in ast.constraints)
            type_parameter_constraints_clause(x);
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        formals(ast.f);
        // InputElement ast.id
        type(ast.ty);
        // [Bind1] Method ast.sym
        // [Emit] MethodBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Node generic_method_declaration(generic_method_declaration ast) {
        foreach (type_parameter x in ast.typeparams)
            type_parameter(x);
        foreach (type_parameter_constraints_clause x in ast.constraints)
            type_parameter_constraints_clause(x);
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        if (ast.body != null)
            statement(ast.body);
        member_name(ast.name);
        formals(ast.parms);
        type(ast.ty);
        // [Bind1] Method ast.sym
        // [Emit] MethodBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    FieldFlags getFieldFlags(stringList modifiers) {
        FieldFlags flags = 0;
        foreach (string mod in modifiers)
            switch (mod) {
            case "private": flags |= FieldFlags.Private; break;
            case "public": flags |= FieldFlags.Public; break;
            case "protected":
                if (modifiers.Contains("internal"))
                    flags |= FieldFlags.FamORAssem;
                else
                    flags |= FieldFlags.Family;
                break;
            case "internal":
                if (modifiers.Contains("protected"))
                    flags |= FieldFlags.FamORAssem;
                else
                    flags |= FieldFlags.Assembly;
                break;
            case "static": flags |= FieldFlags.Static; break;
        }
        return flags;
    }
    MethodFlags getMethodFlags(stringList modifiers) {
        MethodFlags flags = 0;
        foreach (string mod in modifiers)
            switch (mod) {
            case "private": flags |= MethodFlags.Private; break;
            case "public": flags |= MethodFlags.Public; break;
            case "protected":
                if (modifiers.Contains("internal"))
                    flags |= MethodFlags.FamORAssem;
                else
                    flags |= MethodFlags.Family;
                break;
            case "internal":
                if (modifiers.Contains("protected"))
                    flags |= MethodFlags.FamORAssem;
                else
                    flags |= MethodFlags.Assembly;
                break;
            case "static": flags |= MethodFlags.Static; break;
            case "override":
            case "virtual": flags |= MethodFlags.Virtual; break;
            case "new": flags |= MethodFlags.NewSlot; break;
            case "abstract": flags |= MethodFlags.Abstract; break;
            case "sealed": flags |= MethodFlags.Final; break;
            }
        return flags;
    }
    public TypeFlags getTypeFlags(stringList modifiers, bool nested) {
        TypeFlags flags = 0;
        foreach (string mod in modifiers)
            switch (mod) {
            case "private":
                flags |= nested ? TypeFlags.NestedPrivate : TypeFlags.NotPublic; break;
            case "public":
                flags |= nested ? TypeFlags.NestedPublic : TypeFlags.Public; break;
            case "protected":
                if (nested)
                    flags |= modifiers.Contains("internal") ? TypeFlags.NestedFamORAssem : TypeFlags.NestedFamily;
                break;
            case "internal":
                if (nested)
                    flags |= modifiers.Contains("protected") ? TypeFlags.NestedFamORAssem : TypeFlags.NestedAssembly;
                break;
            case "sealed": flags |= TypeFlags.Sealed; break;
            case "abstract": flags |= TypeFlags.Abstract; break;
        }
        return flags;
    }
    Statement goto_case_statement(goto_case_statement ast) {
        return new GotoCase(expression(ast.expr));
    }
    Statement goto_default_statement(goto_default_statement ast) {
        return new GotoCase(null);
    }
    Statement goto_statement(goto_statement ast) {
        return new Goto(identifier(ast.id));
    }
    Identifier identifier(InputElement id) {
        return new Identifier(id.str,
            new SourceContext(document, id.coord.line, id.coord.column,
                id.coord.line, id.coord.column + id.str.Length));
    }
    Statement if_statement(if_statement ast) {
        Expression expr = expression(ast.expr);
        System.Compiler.Block thenpart = block(ast.thenpart);
        if (ast.elsepart != null)
            return new If(expr, thenpart, block(ast.elsepart));
        else
            return new If(expr, thenpart, null);
    }
    Expression implicit_cast_expression(implicit_cast_expression ast) {
        if (ast.ty != null)
            type(ast.ty);
        expression(ast.expr);
        // [Typecheck,MayBeNull] Method ast.method
        // Boolean ast.valueUsed
        // [Typecheck] Type ast.typ
        // [MayBeNull,Typecheck] Object ast.value
        return null;
    }
    Node implicit_declarator(implicit_declarator ast) {
        // InputElement ast.id1
        type(ast.t1);
        // [Bind1] Formal ast.sym
        type(ast.ty);
        // [Bind1] Method ast.method
        return null;
    }
    Node indexer(indexer ast) {
        formals(ast.f);
        if (ast.interfacename != null)
            name_type(ast.interfacename);
        type(ast.ty);
        return null;
    }
    Node indexer_declaration(indexer_declaration ast) {
        foreach (accessor_declaration x in ast.accessors)
            accessor_declaration(x);
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        indexer(ast.i);
        // [Emit] PropertyBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    TypeNode int_type(int_type ast) {
        return SystemTypes.Int32;
    }
    Expression integer_literal(integer_literal ast) {
        ulong n;
        string str = ast.token.str;
        if (str.StartsWith("0x"))
            n = UInt64.Parse(str.Substring(2), System.Globalization.NumberStyles.HexNumber, null);
        else
            n = UInt64.Parse(str);
        string suffix = null;
        if (str.EndsWith("ul") || str.EndsWith("lu"))
            suffix = "ul";
        else if (str.EndsWith("u") || str.EndsWith("l"))
            suffix = str.Substring(str.Length - 1);
        if (n <= int.MaxValue && suffix == null)
            return new Literal((uint)n, SystemTypes.Int32);
        else if (n <= uint.MaxValue && (suffix == null || suffix == "u"))
            return new Literal((uint)n, SystemTypes.UInt32);
        else if (n <= long.MaxValue && (suffix == null || suffix == "l"))
            return new Literal((long)n, SystemTypes.Int64);
        else
            return new Literal(n, SystemTypes.UInt64);
    }
    Node interface_declaration(interface_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        foreach (type_parameter x in ast.typeparams)
            type_parameter(x);
        foreach (type_parameter_constraints_clause x in ast.constraints)
            type_parameter_constraints_clause(x);
        foreach (declaration x in ast.body)
            declaration(x);
        // InputElement ast.id
        foreach (type x in ast.interfaces)
            type(x);
        // [Bind1] InterfaceType ast.sym
        // [Emit] Type ast.type
        // InputElementList ast.mods
        return null;
    }
    Node interface_event_declaration(interface_event_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        // InputElement ast.id
        type(ast.ty);
        // [Bind1] Event ast.sym
        // [Emit] EventBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Node interface_indexer_declaration(interface_indexer_declaration ast) {
        foreach (accessor_declaration x in ast.accessors)
            accessor_declaration(x);
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        formals(ast.f);
        type(ast.ty);
        // [Emit] PropertyBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Node interface_method_declaration(interface_method_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        formals(ast.f);
        // InputElement ast.id
        type(ast.ty);
        // [Bind1] Method ast.sym
        // [Emit] MethodBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Node interface_property_declaration(interface_property_declaration ast) {
        foreach (accessor_declaration x in ast.accessors)
            accessor_declaration(x);
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        // InputElement ast.id
        type(ast.ty);
        // [Bind1] Property ast.sym
        // [Emit] PropertyBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Expression invocation_expression(invocation_expression ast) {
        ExpressionList args = new ExpressionList();
        foreach (argument x in ast.args)
            args.Add(argument(x));
        return new MethodCall(expression(ast.expr), args);
    }
    Expression is_expression(is_expression ast) {
        return new BinaryExpression(expression(ast.expr),
            new MemberBinding(null, type(ast.ty)), NodeType.Is);
    }
    Statement labeled_statement(labeled_statement ast) {
        LabeledStatement result = new LabeledStatement();
        result.Label = identifier(ast.label);
        result.Statement = statement(ast.stmt);
        return result;
    }
    Expression literal(literal ast) {
             if (ast is boolean_literal) return boolean_literal((boolean_literal)ast);
        else if (ast is character_literal) return character_literal((character_literal)ast);
        else if (ast is integer_literal) return integer_literal((integer_literal)ast);
        else if (ast is null_literal) return null_literal((null_literal)ast);
        else if (ast is real_literal) return real_literal((real_literal)ast);
        else if (ast is string_literal) return string_literal((string_literal)ast);
        else throw new ArgumentException();
    }
    Statement local_statement(local_statement ast) {
        LocalDeclarationsStatement result = new LocalDeclarationsStatement();
        result.Constant = false;
        result.Type = type(ast.ty);
        result.Declarations = new LocalDeclarationList();
        foreach (var_declarator x in ast.vars)
            result.Declarations.Add(var_declarator(x));
        return result;
    }
    Statement lock_statement(lock_statement ast) {
        Lock result = new Lock();
        result.Guard = expression(ast.expr);
        result.Body = block(ast.body);
        return result;
    }
    TypeNode long_type(long_type ast) {
        return SystemTypes.Int64;
    }
    Expression member_access(member_access ast) {
             if (ast is expr_access) return expr_access((expr_access)ast);
        else if (ast is pointer_access) return pointer_access((pointer_access)ast);
        else if (ast is predefined_access) return predefined_access((predefined_access)ast);
        else throw new ArgumentException();
    }
    Node member_name(member_name ast) {
        // InputElement ast.id
        if (ast.ty != null)
            type(ast.ty);
        // [Bind2] InterfaceType ast.sym
        return null;
    }
    Node method_declaration(method_declaration ast) {
        System.Compiler.Method result = new System.Compiler.Method();
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        result.Flags = getMethodFlags(stringList(ast.mods));
        if (ast.body != null)
            result.Body = block(ast.body);
        member_name(ast.name);
        result.Name = identifier(ast.name.id);
        result.Parameters = formals(ast.parms);
        for (int i = 0; i < result.Parameters.Length; i++)
            result.Parameters[i].DeclaringMethod = result;
        result.ReturnType = type(ast.ty);
        return result;
    }
    TypeNode name_type(name_type ast) {
        dotted_name(ast.name);
        // [Bind2] Type ast.sym
        return null;
    }
    Node named_argument(named_argument ast) {
        expression(ast.expr);
        // InputElement ast.id
        return null;
    }
    Node namespace_body(namespace_body ast) {
        foreach (declaration x in ast.declarations)
            declaration(x);
        foreach (using_directive x in ast.ud)
            using_directive(x);
        return null;
    }
    Node namespace_declaration(namespace_declaration ast) {
        dotted_name(ast.id);
        namespace_body(ast.nb);
        // [Bind1] NameSpace ast.sym
        // InputElementList ast.mods
        return null;
    }
    Node namespace_directive(namespace_directive ast) {
        dotted_name(ast.name);
        // [Bind1] NameSpace ast.sym
        return null;
    }
    Expression new_expression(new_expression ast) {
        ExpressionList args = new ExpressionList();
        foreach (argument x in ast.args)
            args.Add(argument(x));
        return new Construct(new Literal(type(ast.ty), SystemTypes.Type), args);
    }
    Expression null_literal(null_literal ast) {
        return new Literal(null, SystemTypes.Object);
    }
    TypeNode object_type(object_type ast) {
        return SystemTypes.Object;
    }
    Node operator_declaration(operator_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        if (ast.block != null)
            statement(ast.block);
        operator_declarator(ast.op);
        // [Bind1] Method ast.sym
        // InputElementList ast.mods
        return null;
    }
    Node operator_declarator(operator_declarator ast) {
             if (ast is binary_declarator) return binary_declarator((binary_declarator)ast);
        else if (ast is explicit_declarator) return explicit_declarator((explicit_declarator)ast);
        else if (ast is implicit_declarator) return implicit_declarator((implicit_declarator)ast);
        else if (ast is unary_declarator) return unary_declarator((unary_declarator)ast);
        else throw new ArgumentException();
    }
    Parameter parameter(parameter ast) {
             if (ast is arglist_parameter) return arglist_parameter((arglist_parameter)ast);
        else if (ast is fixed_parameter) return fixed_parameter((fixed_parameter)ast);
        else if (ast is params_parameter) return params_parameter((params_parameter)ast);
        else throw new ArgumentException();
    }
    Parameter params_parameter(params_parameter ast) {
        Parameter result = new Parameter(identifier(ast.id), type(ast.ty));
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        return result;
    }
    Expression pointer_access(pointer_access ast) {
        AddressDereference addr = new AddressDereference();
        addr.Address = expression(ast.expr);
        Expression result = new QualifiedIdentifier(addr, identifier(ast.id));
        if (ast.typeargs != null) {
            foreach (type x in ast.typeargs)
                type(x);
        }
        return result;
    }
    TypeNode pointer_type(pointer_type ast) {
        return new PointerTypeExpression(type(ast.ty));
    }
    Expression post_expression(post_expression ast) {
        NodeType op;
        switch (ast.op.str) {
        case "++":  op = NodeType.Increment; break;
        case "--":  op = NodeType.Decrement; break;
        default:    op = NodeType.Nop; break;
        }
        return new UnaryExpression(expression(ast.expr), op);
    }
    Expression pre_expression(pre_expression ast) {
        NodeType op;
        switch (ast.op.str) {
        case "++":  op = NodeType.Increment; break;
        case "--":  op = NodeType.Decrement; break;
        default:    op = NodeType.Nop; break;
        }
        return new UnaryExpression(expression(ast.expr), op);
    }
    Expression predefined_access(predefined_access ast) {
        Expression result = new QualifiedIdentifier(
            new Literal(type(ast.predefined.str), SystemTypes.Type),
            identifier(ast.id));
        if (ast.typeargs != null) {
            foreach (type x in ast.typeargs)
                type(x);
        }
        return result;
    }
    Node property_declaration(property_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        foreach (accessor_declaration x in ast.decls)
            accessor_declaration(x);
        member_name(ast.name);
        type(ast.ty);
        // [Bind1] Property ast.sym
        // [Emit] PropertyBuilder ast.builder
        // InputElementList ast.mods
        return null;
    }
    Node qualified_alias_member(qualified_alias_member ast) {
        // InputElement ast.qualifier
        if (ast.left != null)
            dotted_name(ast.left);
        // InputElement ast.right
        if (ast.typeargs != null)
            foreach (type x in ast.typeargs)
                type(x);
        // [Bind2] Symbol ast.sym
        return null;
    }
    Node qualified_name(qualified_name ast) {
        // InputElement ast.qualifier
        // InputElement ast.id
        if (ast.typeargs != null)
            foreach (type x in ast.typeargs)
                type(x);
        // [Bind2] Symbol ast.sym
        // [Typecheck,MayBeNull] Method ast.method
        // Boolean ast.valueUsed
        // [Typecheck] Type ast.typ
        // [MayBeNull,Typecheck] Object ast.value
        return null;
    }
    Expression real_literal(real_literal ast) {
        string str = ast.token.str;
        try {
            if (str.EndsWith("m"))
                return new Literal(Decimal.Parse(str), SystemTypes.Decimal);
            else if (str.EndsWith("f"))
                return new Literal(Single.Parse(str), SystemTypes.Single);
            else
                return new Literal(Double.Parse(str), SystemTypes.Double);
        } catch (OverflowException) {
            return new Literal(0.0, SystemTypes.Double);
        }
    }
    Statement resource(resource ast) {
             if (ast is resource_decl) return resource_decl((resource_decl)ast);
        else if (ast is resource_expr) return resource_expr((resource_expr)ast);
        else throw new ArgumentException();
    }
    Statement resource_decl(resource_decl ast) {
        Statement result = local_statement(ast.local);
        result.SourceContext = context(ast);
        return result;
    }
    Statement resource_expr(resource_expr ast) {
        Statement result = expressionstatement(ast.expr);
        result.SourceContext = context(ast);
        return result;
    }
    Statement return_statement(return_statement ast) {
        if (ast.expr != null)
            return new Return(expression(ast.expr));
        else
            return new Return();
    }
    TypeNode sbyte_type(sbyte_type ast) {
        return SystemTypes.Int8;
    }
    TypeNode short_type(short_type ast) {
        return SystemTypes.Int16;
    }
    Expression simple_name(simple_name ast) {
        Expression result = identifier(ast.id);
        if (ast.typeargs != null) {
            foreach (type x in ast.typeargs)
                type(x);
        }
        return result;
    }
    Expression sizeof_expression(sizeof_expression ast) {
        return new UnaryExpression(
            new MemberBinding(null, typeexpression(ast.ty)), NodeType.Sizeof);
    }
    Expression stackalloc_initializer(stackalloc_initializer ast) {
        type(ast.ty);
        return expression(ast.expr);
    }
    Statement statement(statement ast) {
        Statement result = null;
             if (ast is block_statement) result = block_statement((block_statement)ast);
        else if (ast is break_statement) result = break_statement((break_statement)ast);
        else if (ast is checked_statement) result = checked_statement((checked_statement)ast);
        else if (ast is const_statement) result = const_statement((const_statement)ast);
        else if (ast is continue_statement) result = continue_statement((continue_statement)ast);
        else if (ast is do_statement) result = do_statement((do_statement)ast);
        else if (ast is empty_statement) result = empty_statement((empty_statement)ast);
        else if (ast is expression_statement) result = expression_statement((expression_statement)ast);
        else if (ast is fixed_statement) result = fixed_statement((fixed_statement)ast);
        else if (ast is for_statement) result = for_statement((for_statement)ast);
        else if (ast is foreach_statement) result = foreach_statement((foreach_statement)ast);
        else if (ast is goto_case_statement) result = goto_case_statement((goto_case_statement)ast);
        else if (ast is goto_default_statement) result = goto_default_statement((goto_default_statement)ast);
        else if (ast is goto_statement) result = goto_statement((goto_statement)ast);
        else if (ast is if_statement) result = if_statement((if_statement)ast);
        else if (ast is labeled_statement) result = labeled_statement((labeled_statement)ast);
        else if (ast is local_statement) result = local_statement((local_statement)ast);
        else if (ast is lock_statement) result = lock_statement((lock_statement)ast);
        else if (ast is return_statement) result = return_statement((return_statement)ast);
        else if (ast is switch_statement) result = switch_statement((switch_statement)ast);
        else if (ast is throw_statement) result = throw_statement((throw_statement)ast);
        else if (ast is try_statement) result = try_statement((try_statement)ast);
        else if (ast is unchecked_statement) result = unchecked_statement((unchecked_statement)ast);
        else if (ast is unsafe_statement) result = unsafe_statement((unsafe_statement)ast);
        else if (ast is using_statement) result = using_statement((using_statement)ast);
        else if (ast is while_statement) result = while_statement((while_statement)ast);
        else if (ast is yield_statement) result = yield_statement((yield_statement)ast);
        else throw new ArgumentException();
        result.SourceContext = context(ast);
        return result;
    }
    Expression string_literal(string_literal ast) {
        bool errorFlag;
        return new Literal(typecheck.stringLiteral(ast.token.str, out errorFlag), SystemTypes.String);
    }
    TypeNode string_type(string_type ast) {
        return SystemTypes.String;
    }
    stringList stringList(InputElementList srclist) {
        stringList list = new stringList();
        foreach (InputElement e in srclist)
            list.Add(e.str);
        return list;
    }
    Node struct_declaration(struct_declaration ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        foreach (type_parameter x in ast.typeparams)
            type_parameter(x);
        foreach (type_parameter_constraints_clause x in ast.constraints)
            type_parameter_constraints_clause(x);
        foreach (declaration x in ast.body)
            declaration(x);
        // InputElement ast.id
        foreach (type x in ast.interfaces)
            type(x);
        // [Bind1] StructType ast.sym
        // [Emit] Type ast.type
        // InputElementList ast.mods
        return null;
    }
    SwitchCase switch_default(switch_default ast) {
        return new SwitchCase(null, null);
    }
    SwitchCase switch_expression(switch_expression ast) {
        return new SwitchCase(expression(ast.expr), null);
    }
    SwitchCase switch_label(switch_label ast) {
             if (ast is switch_default) return switch_default((switch_default)ast);
        else if (ast is switch_expression) return switch_expression((switch_expression)ast);
        else throw new ArgumentException();
    }
    void switch_section(switch_section ast, SwitchCaseList cases) {
        foreach (switch_label x in ast.labels)
            cases.Add(switch_label(x));
        StatementList stmts = new StatementList();
        cases[cases.Length-1].Body = new System.Compiler.Block(stmts);
        foreach (statement x in ast.stmts)
            stmts.Add(statement(x));
    }
    Statement switch_statement(switch_statement ast) {
        Switch result = new Switch(expression(ast.expr), new SwitchCaseList());
        foreach (switch_section x in ast.sections)
            switch_section(x, result.Cases);
        return result;
    }
    Expression this_access(this_access ast) {
        return new This();
    }
    Node this_initializer(this_initializer ast) {
        foreach (argument x in ast.args)
            argument(x);
        // [Typecheck] Constructor ast.method
        return null;
    }
    Statement throw_statement(throw_statement ast) {
        if (ast.expr != null)
            return new Throw(expression(ast.expr));
        else
            return new Throw();
    }
    Statement try_statement(try_statement ast) {
        Try result = new Try();
        result.TryBlock = block(ast.block);
        if (ast.catches != null)
            result.Catchers = catch_clauses(ast.catches);
        if (ast.finally_block != null)
            result.Finally = finally_clause(ast.finally_block);
        return result;
    }
    TypeNode type(type ast) {
        TypeNode result = null;
             if (ast is array_type) result = array_type((array_type)ast);
        else if (ast is bool_type) result = bool_type((bool_type)ast);
        else if (ast is byte_type) result = byte_type((byte_type)ast);
        else if (ast is char_type) result = char_type((char_type)ast);
        else if (ast is constructor_constraint) result = constructor_constraint((constructor_constraint)ast);
        else if (ast is decimal_type) result = decimal_type((decimal_type)ast);
        else if (ast is double_type) result = double_type((double_type)ast);
        else if (ast is float_type) result = float_type((float_type)ast);
        else if (ast is int_type) result = int_type((int_type)ast);
        else if (ast is long_type) result = long_type((long_type)ast);
        else if (ast is name_type) result = name_type((name_type)ast);
        else if (ast is object_type) result = object_type((object_type)ast);
        else if (ast is pointer_type) result = pointer_type((pointer_type)ast);
        else if (ast is sbyte_type) result = sbyte_type((sbyte_type)ast);
        else if (ast is short_type) result = short_type((short_type)ast);
        else if (ast is string_type) result = string_type((string_type)ast);
        else if (ast is type_parameter) result = type_parameter((type_parameter)ast);
        else if (ast is uint_type) result = uint_type((uint_type)ast);
        else if (ast is ulong_type) result = ulong_type((ulong_type)ast);
        else if (ast is ushort_type) result = ushort_type((ushort_type)ast);
        else if (ast is void_pointer_type) result = void_pointer_type((void_pointer_type)ast);
        else if (ast is void_type) result = void_type((void_type)ast);
        else throw new ArgumentException();
        result.SourceContext = context(ast);
        return result;
    }
    TypeNode type(string id) {
        switch (id) {
        case "bool":    return SystemTypes.Boolean;
        case "decimal": return SystemTypes.Decimal;
        case "sbyte":   return SystemTypes.Int8;
        case "byte":    return SystemTypes.UInt8;
        case "short":   return SystemTypes.Int16;
        case "ushort":  return SystemTypes.UInt16;
        case "int":     return SystemTypes.Int32;
        case "uint":    return SystemTypes.UInt32;
        case "long":    return SystemTypes.Int64;
        case "ulong":   return SystemTypes.UInt64;
        case "char":    return SystemTypes.Char;
        case "float":   return SystemTypes.Single;
        case "double":  return SystemTypes.Double;
        case "object":  return SystemTypes.Object;
        case "string":  return SystemTypes.String;
        case "void":    return SystemTypes.Void;
        default:        return null;
        }
    }
    Node type_declaration(type_declaration ast) {
             if (ast is class_declaration) return class_declaration((class_declaration)ast);
        else if (ast is delegate_declaration) return delegate_declaration((delegate_declaration)ast);
        else if (ast is enum_declaration) return enum_declaration((enum_declaration)ast);
        else if (ast is interface_declaration) return interface_declaration((interface_declaration)ast);
        else if (ast is struct_declaration) return struct_declaration((struct_declaration)ast);
        else throw new ArgumentException();
    }
    TypeExpression typeexpression(type ast) {
        TypeNode t = type(ast);
        TypeExpression result = new TypeExpression(new Literal(t, SystemTypes.Type), t.SourceContext);
        result.Name = t.Name;
        return result;
    }
    TypeNode type_parameter(type_parameter ast) {
        foreach (attribute_section x in ast.attrs)
            attribute_section(x);
        // InputElement ast.id
        // [Bind2] Type ast.sym
        return null;
    }
    Node type_parameter_constraints_clause(type_parameter_constraints_clause ast) {
        // InputElement ast.id
        foreach (type x in ast.constraints)
            type(x);
        return null;
    }
    Expression typeof_expression(typeof_expression ast) {
        return new UnaryExpression(
            new MemberBinding(null, typeexpression(ast.ty)), NodeType.Typeof);
    }
    TypeNode uint_type(uint_type ast) {
        return SystemTypes.UInt32;
    }
    TypeNode ulong_type(ulong_type ast) {
        return SystemTypes.UInt64;
    }
    Node unary_declarator(unary_declarator ast) {
        // InputElement ast.id1
        // InputElement ast.op
        type(ast.t1);
        // [Bind1] Formal ast.sym
        type(ast.ty);
        // [Bind1] Method ast.method
        return null;
    }
    Expression unary_expression(unary_expression ast) {
        NodeType op;
        switch (ast.op.str) {
        case "+":   op = NodeType.UnaryPlus; break;
        case "~":   op = NodeType.Not; break;
        case "-":   op = NodeType.Neg; break;
        case "!":   op = NodeType.LogicalNot; break;
        case "&":   op = NodeType.AddressOf; break;
        default:    op = NodeType.Nop; break;
        }
        return new UnaryExpression(expression(ast.expr), op);
    }
    Expression unchecked_expression(unchecked_expression ast) {
        BlockExpression result = new BlockExpression();
        result.Block = new System.Compiler.Block(new StatementList(expressionstatement(ast.expr)), false, true);
        return result;
    }
    Statement unchecked_statement(unchecked_statement ast) {
        System.Compiler.Block result = block(ast.stmt);
        result.Checked = false;
        result.SuppressCheck = true;
        return result;
    }
    Statement unsafe_statement(unsafe_statement ast) {
        return block(ast.block);
    }
    TypeNode ushort_type(ushort_type ast) {
        return SystemTypes.UInt16;
    }
    Node using_directive(using_directive ast) {
             if (ast is alias_directive) return alias_directive((alias_directive)ast);
        else if (ast is namespace_directive) return namespace_directive((namespace_directive)ast);
        else throw new ArgumentException();
    }
    Statement using_statement(using_statement ast) {
        ResourceUse result = new ResourceUse();
        result.ResourceAcquisition = resource(ast.r);
        result.Body = block(ast.body);
        return result;
    }
    LocalDeclaration var_declarator(var_declarator ast) {
        if (ast.init != null)
            return new LocalDeclaration(identifier(ast.id), variable_initializer(ast.init));
        else
            return new LocalDeclaration(identifier(ast.id), null);
    }
    Expression variable_initializer(variable_initializer ast) {
             if (ast is array_initializer) return array_initializer((array_initializer)ast);
        else if (ast is expr_initializer) return expr_initializer((expr_initializer)ast);
        else if (ast is stackalloc_initializer) return stackalloc_initializer((stackalloc_initializer)ast);
        else throw new ArgumentException();
    }
    TypeNode void_pointer_type(void_pointer_type ast) {
        return new PointerTypeExpression(SystemTypes.Void);
    }
    TypeNode void_type(void_type ast) {
        return SystemTypes.Void;
    }
    Statement while_statement(while_statement ast) {
        return new While(expression(ast.expr), block(ast.body));
    }
    Statement yield_break_statement(yield_break_statement ast) {
        return new Yield();
    }
    Statement yield_return_statement(yield_return_statement ast) {
        return new Yield(expression(ast.expr));
    }
    Statement yield_statement(yield_statement ast) {
             if (ast is yield_return_statement) return yield_return_statement((yield_return_statement)ast);
        else if (ast is yield_break_statement) return yield_break_statement((yield_break_statement)ast);
        else throw new ArgumentException();
    }
}
