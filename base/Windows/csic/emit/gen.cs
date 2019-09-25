using System;
using System.IO;
using System.Collections;
using System.Reflection.Emit;

public class temporary: expression {
	public temporary(Type typ, int var) {
		this.typ = typ;
		this.var = var;
	}
	public int var = 0;
}

abstract public class gen {
	Stack asts;	// top element is current ast node
	bool checkoverflow = false;
	MessageWriter msg;
	int nextlab = 1;
	BuiltinTypes T;
	int retlab = -1;	// return label for current method, if return inside try
	int retvar = -1;	// return value for current method, if return inside try

	public gen(BuiltinTypes T, MessageWriter msg) : this(T, msg, new Stack()) {}
	public gen(BuiltinTypes T, MessageWriter msg, Stack asts) {
		this.T = T;
		this.msg = msg;
		this.asts = asts;
	}
	public virtual bool checking {
		get { return checkoverflow; }
		set { checkoverflow = value; }
	}
	abstract public void EmitCreateArray(ArrayType ty, Type ety, int rank);
	public virtual void array_create(ArrayType aty, array_initializer ast) {
		if (aty.rank > 1)
			EmitCreateArray(aty, aty.elementType, aty.rank);
		else
			Emit(OpCodes.Newarr, aty.elementType);
		if (ast != null)
			array_init(ast, aty, 0, new int[aty.rank]);
	}
	public virtual void array_creation_expression1(array_creation_expression1 ast) {
		foreach (expression x in ast.exprs)
			expression(x);
		array_create((ArrayType)ast.typ, ast.init);
	}
	public virtual void array_creation_expression2(array_creation_expression2 ast) {
		array_initializer(ast.init);
	}
	public virtual void array_initializer(array_initializer ast) {
		ArrayType aty = (ArrayType)ast.typ;
		for (array_initializer x = ast; x != null; ) {
			Emit(OpCodes.Ldc_I4, x.a.Count);
			x = x.a[0] as array_initializer;
		}
		array_create(aty, ast);
	}
	public virtual void array_init(array_initializer ast, ArrayType aty, int index, int[] indices) {
		if (ast.a.Count > 0 && ast.a[0] is array_initializer) {
			foreach (array_initializer x in ast.a) {
				array_init(x, aty, index + 1, indices);
				indices[index]++;
			}
		} else {
			indices[index] = 0;
			foreach (expr_initializer x in ast.a) {
				Emit(OpCodes.Dup);
				foreach (int i in indices)
					Emit(OpCodes.Ldc_I4, i);
				EmitStoreElement(aty, x.expr);
				indices[index]++;
			}
		}
	}
	public virtual void as_expression(as_expression ast) {
		expression(ast.expr);
		Emit(OpCodes.Isinst, ast.sym);
	}
	public virtual void assignment_expression(assignment_expression ast) {
		expression(ast.e1, ast.e2);
		if (ast.valueUsed)
			expression(ast.e2);
	}
	public virtual void base_access(base_access ast) {
		this_access();
		Type ty = currentClass(ast);
		if (ty is StructType) {
			Emit(OpCodes.Ldobj, ty);
			Emit(OpCodes.Box, ty);
		}
	}
	public virtual void base_initializer(base_initializer ast) {
		this_access();
		EmitArgumentList(ast.method, ast.args);
		EmitCall(ast.method);
	}
	public virtual object BeginTry() { return genLabel(1); }
	public virtual object BeginFinally(object handle) {
		gotoLabel(OpCodes.Leave, (int)handle);
		return handle;
	}
	public virtual void binary_expression(binary_expression ast, int trueLabel, int falseLabel) {
		switch (ast.op.str) {
		case "&&":
			if (falseLabel != 0) {
				expression(ast.e1, 0, falseLabel);
				expression(ast.e2, 0, falseLabel);
			} else if (trueLabel != 0) {
				expression(ast.e1, 0, falseLabel = genLabel(1));
				expression(ast.e2, trueLabel, 0);
				defLabel(falseLabel);
			} else
				boolean_value(ast);
			return;
		case "||":
			if (trueLabel != 0) {
				expression(ast.e1, trueLabel, 0);
				expression(ast.e2, trueLabel, 0);
			} else if (falseLabel != 0) {
				expression(ast.e1, trueLabel = genLabel(1), 0);
				expression(ast.e2, 0, falseLabel);
				defLabel(trueLabel);
			} else
				boolean_value(ast);
			return;
		case  "<": comparison(ast.e1.typ.IsUnsigned ? OpCodes.Blt_Un : OpCodes.Blt, ast.e1.typ.IsUnsigned ? OpCodes.Bge_Un : OpCodes.Bge, ast, trueLabel, falseLabel); return;
		case "<=": comparison(ast.e1.typ.IsUnsigned ? OpCodes.Ble_Un : OpCodes.Ble, ast.e1.typ.IsUnsigned ? OpCodes.Bgt_Un : OpCodes.Bgt, ast, trueLabel, falseLabel); return;
		case  ">": comparison(ast.e1.typ.IsUnsigned ? OpCodes.Bgt_Un : OpCodes.Bgt, ast.e1.typ.IsUnsigned ? OpCodes.Ble_Un : OpCodes.Ble, ast, trueLabel, falseLabel); return;
		case ">=": comparison(ast.e1.typ.IsUnsigned ? OpCodes.Bge_Un : OpCodes.Bge, ast.e1.typ.IsUnsigned ? OpCodes.Blt_Un : OpCodes.Blt, ast, trueLabel, falseLabel); return;
		case "==": comparison(OpCodes.Beq, OpCodes.Bne_Un, ast, trueLabel, falseLabel); return;
		case "!=": comparison(OpCodes.Bne_Un, OpCodes.Beq, ast, trueLabel, falseLabel); return;
		case ",":
			expression(ast.e1);
			if (ast.e1.valueUsed)
				Emit(OpCodes.Pop);
			expression(ast.e2);
			return;
		}
		expression(ast.e1);
		expression(ast.e2);
		binary_operator(ast.op.str, ast.typ, ast.method);
	}
	public virtual void binary_operator(string op, Type ty, Method method) {
		if (method != null && method.declSpace != null) {
			EmitCall(method);
			return;
		}
		if (checking && (ty.IsSigned || ty.IsUnsigned))
			switch (op) {
			case "+": Emit(ty.IsUnsigned ? OpCodes.Add_Ovf_Un : OpCodes.Add_Ovf); return;
			case "-": Emit(ty.IsUnsigned ? OpCodes.Sub_Ovf_Un : OpCodes.Sub_Ovf); return;
			case "*": Emit(ty.IsUnsigned ? OpCodes.Mul_Ovf_Un : OpCodes.Mul_Ovf); return;
			}
		switch (op) {
		case  "+":
			if (ty is DelegateType) {
				EmitCall(T.Delegate.FindMethod("Combine", T.Delegate, T.Delegate));
				EmitCast(T.Delegate, ty);
			} else
				Emit(OpCodes.Add);
			break;
		case  "-":
			if (ty is DelegateType) {
				EmitCall(T.Delegate.FindMethod("Remove", T.Delegate, T.Delegate));
				EmitCast(T.Delegate, ty);
			} else
				Emit(OpCodes.Sub);
			break;
		case  "*": Emit(OpCodes.Mul); break;
		case  "/": Emit(ty.IsUnsigned ? OpCodes.Div_Un : OpCodes.Div); break;
		case  "%": Emit(ty.IsUnsigned ? OpCodes.Rem_Un : OpCodes.Rem); break;
		case "<<": Emit(OpCodes.Shl); break;
		case ">>": Emit(ty.IsUnsigned ? OpCodes.Shr_Un : OpCodes.Shr); break;
		case  "&": Emit(OpCodes.And); break;
		case  "|": Emit(OpCodes.Or); break;
		case  "^": Emit(OpCodes.Xor); break;
		default: Debug.Fail(String.Format("unknown binary operator '{0}'", op)); break;
		}
	}
	public virtual void block_statement(block_statement ast) {
		foreach (statement s in ast.stmts)
			statement(s);
	}
	public virtual void boolean_literal(boolean_literal ast) {
		Emit(OpCodes.Ldc_I4, ast.token.str == "true" ? 1 : 0);
	}
	public virtual void boolean_value(binary_expression ast) {
		if (ast.method != null && ast.method.Type == T.Bool && ast.method.declSpace != null) {
			expression(ast.e1);
			expression(ast.e2);
			EmitCall(ast.method);
		} else {
			int lab = genLabel(2);
			expression(ast, 0, lab);
			Emit(OpCodes.Ldc_I4_1);
			gotoLabel(lab + 1);
			defLabel(lab);
			Emit(OpCodes.Ldc_I4_0);
			defLabel(lab + 1);
		}
	}
	public virtual void break_statement(break_statement ast) {
		if (ast.stmt != null)
			gotoLabel(ast.exitstry ? OpCodes.Leave : OpCodes.Br, ast.stmt.lab + 2);
	}
	public virtual void cast_expression(cast_expression ast) {
		expression(ast.expr);
		EmitCast(ast.expr.typ, ast.sym);
	}
	public virtual void catch_clause(Type ty, Local sym, statement block, object handle) {
		if (sym == null)
			Emit(OpCodes.Pop);
		else {
			sym.ordinal = newLocal(sym.Type, sym.Name);			
			EmitStore(sym);
		}
		statement(block);
	}
	public virtual void catch_clause(catch_clause ast, object handle) {
		catch_clause(ast.ty.sym, ast.sym, ast.block, handle);
	}
	public virtual void catch_clauses(catch_clauses ast, object handle) {
		foreach (catch_clause x in ast.specifics)
			catch_clause(x, handle);
		if (ast.general != null)
			catch_clause(T.Object, null, ast.general, handle);
	}
	public virtual void character_literal(character_literal ast) {
		Emit(OpCodes.Ldc_I4, (int)(char)ast.value);
	}
	public virtual void checked_expression(checked_expression ast, bool lvalue) {
		bool save = checking;
		checking = true;
		expression(ast.expr, lvalue);
		checking = save;
	}
	public virtual void checked_expression(checked_expression ast, expression rhs) {
		bool save = checking;
		checking = true;
		expression(ast.expr, rhs);
		checking = save;
	}
	public virtual void checked_statement(checked_statement ast) {
		bool save = checking;
		checking = true;
		statement(ast.stmt);
		checking = save;
	}
	public virtual void comparison(OpCode inst, OpCode flip, binary_expression ast, int trueLabel, int falseLabel) {
		if (trueLabel == 0 && falseLabel == 0)
			boolean_value(ast);
		else {
			expression(ast.e1);
			expression(ast.e2);
			if (ast.method != null && ast.method.declSpace != null) {
				EmitCall(ast.method);
				if (ast.method.Type == T.Bool) {
					inst = OpCodes.Brtrue;
					flip = OpCodes.Brfalse;
				}
			}
			if (trueLabel != 0)
				gotoLabel(inst, trueLabel);
			else
				gotoLabel(flip, falseLabel);
		}
	}
	public virtual void compound_assignment_expression(compound_assignment_expression ast) {
		if (ast.method != null && is_event_access(ast.e1)) {
			if (ast.e1 is simple_name && ((simple_name)ast.e1).sym.IsInstance)
				this_access();
			else if (ast.e1 is expr_access)
				expression(((expr_access)ast.e1).expr);
			expression(ast.e2);
			EmitCall(ast.method);
		} else {
			expression(ast.e1);
			expression(ast.e2);
			binary_operator(ast.op.str.TrimEnd('='), ast.typ, ast.opmethod);
			temporary rhs = new temporary(ast.typ, newLocal(ast.typ));
			EmitStore(rhs.var);
			expression(ast.e1, rhs);
			if (ast.valueUsed)
				expression(rhs);
		}
	}
	public virtual void cond_expression(cond_expression ast) {
		int lab = genLabel(2);
		expression(ast.cond, 0, lab);
		expression(ast.success);
		gotoLabel(lab + 1);
		defLabel(lab);
		expression(ast.failure);
		defLabel(lab + 1);
	}
	public virtual void const_statement(const_statement ast) {
	}
	public virtual void continue_statement(continue_statement ast) {
		if (ast.stmt != null)
			gotoLabel(ast.exitstry ? OpCodes.Leave : OpCodes.Br, ast.stmt.lab + 1);
	}
	public static ClassType currentClass(AST ast) {
		for ( ; ast != null; ast = ast.parent)
			if (ast is class_declaration)
				return ((class_declaration)ast).sym;
			else if (ast is struct_declaration)
				return ((struct_declaration)ast).sym;
			else if (ast is interface_declaration)
				return ((interface_declaration)ast).sym;
		return null;				
	}
	abstract public void defLabel(int lab);
	public virtual void do_statement(do_statement ast) {
		ast.lab = genLabel(3);
		defLabel(ast.lab);
		statement(ast.body);
		defLabel(ast.lab + 1);
		expression(ast.expr, ast.lab, 0);
		defLabel(ast.lab + 2);
	}
	public virtual void element_access(element_access ast, bool lvalue) {
		expression(ast.expr);
		if (ast.get != null) {
			EmitArgumentList(ast.get, ast.exprs);
			if (ast.expr is base_access)
				EmitCall(OpCodes.Call, ast.get);
			else
				EmitCall(ast.get);
		} else if (lvalue && ast.expr.typ is ArrayType) {
			EmitArgumentList(ast.exprs);
			EmitLoadElementAddress((ArrayType)ast.expr.typ);
		} else if (ast.expr.typ is ArrayType) {
			EmitArgumentList(ast.exprs);
			EmitLoadElement((ArrayType)ast.expr.typ);
		}
	}
	public virtual void element_access(element_access ast, expression rhs) {
		expression(ast.expr);
		if (ast.set != null) {
			EmitArgumentList(ast.set, ast.exprs);
			expression(rhs);
			if (ast.expr is base_access)
				EmitCall(OpCodes.Call, ast.set);
			else
				EmitCall(ast.set);
		} else if (ast.expr.typ is ArrayType) {
			EmitArgumentList(ast.exprs);
			EmitStoreElement((ArrayType)ast.expr.typ, rhs);
		}
	}
	abstract public void Emit(OpCode op);
	abstract public void Emit(OpCode op, Constructor x);
	abstract public void Emit(OpCode op, double x);
	abstract public void Emit(OpCode op, float x);
	abstract public void Emit(OpCode op, Field x);
	abstract public void Emit(OpCode op, int x);
	abstract public void Emit(OpCode op, Formal x);
	abstract public void Emit(OpCode op, Local x);
	abstract public void Emit(OpCode op, Method x);
	abstract public void Emit(OpCode op, string x);
	abstract public void Emit(OpCode op, Type x);
	public virtual void EmitArgumentList(argumentList args) {
		foreach (argument a in args)
			expression(a.expr, a.kind != null);
	}
	public virtual void EmitArgumentList(Method m, argumentList args) {
		if (m.IsParams && (args.Count != m.ArgCount
		|| !Type.Equals(m[m.ArgCount-1].Type, args[m.ArgCount-1].expr.typ))) {
			int i;
			for (i = 0; i < m.ArgCount - 1; i++)
				expression(args[i].expr, args[i].kind != null);
			ArrayType last = (ArrayType)m[i].Type;
			Emit(OpCodes.Ldc_I4, args.Count - m.ArgCount + 1);
			Emit(OpCodes.Newarr, last.elementType);
			for ( ; i < args.Count; i++) {
				Emit(OpCodes.Dup);
				Emit(OpCodes.Ldc_I4, i - m.ArgCount + 1);
				EmitStoreElement(last, args[i].expr);
			}
		} else
			EmitArgumentList(args);
	}
	public virtual void EmitCall(Method m) {
		if (m.Is("virtual"))
			EmitCall(OpCodes.Callvirt, m);
		else
			EmitCall(OpCodes.Call, m);
	}
	public virtual void EmitCall(Constructor m) {
		Emit(OpCodes.Call, m);
	}
	public virtual void EmitCall(OpCode inst, Method m) {
		Emit(inst, m);
	}
	public virtual void EmitCast(Type from, Type to) {
		if (Type.Equals(from, to))
			return;
		if (from.IsReferenceType && to.IsValueType) {
			Emit(OpCodes.Unbox, to);
			EmitLoadIndirect(to);
		} else if (from.IsValueType && to.IsReferenceType)
			Emit(OpCodes.Box, from);
		else if (from.IsReferenceType && to.IsReferenceType
		&& from == T.Null || to.InheritsFrom(from) || from.InheritsFrom(to) || from.Implements(to)) {
			if (to.InheritsFrom(from))
				Emit(OpCodes.Castclass, to);
		} else if (from is EnumType && to.IsNumeric)
			EmitCast(((EnumType)from).baseType, to);
		else if (from.IsNumeric && to.IsNumeric) {
			if (to == T.SByte || to == T.Bool)
				Emit(checking ? OpCodes.Conv_Ovf_I1 : OpCodes.Conv_I1);
			else if (to == T.Short)
				Emit(checking ? OpCodes.Conv_Ovf_I2 : OpCodes.Conv_I2);
			else if (to == T.Int)
				Emit(checking ? OpCodes.Conv_Ovf_I4 : OpCodes.Conv_I4);
			else if (to == T.Long)
				Emit(checking ? OpCodes.Conv_Ovf_I8 : OpCodes.Conv_I8);
			else if (to == T.Byte)
				Emit(checking ? OpCodes.Conv_Ovf_U1 : OpCodes.Conv_U1);
			else if (to == T.UShort || to == T.Char)
				Emit(checking ? OpCodes.Conv_Ovf_U2 : OpCodes.Conv_U2);
			else if (to == T.UInt)
				Emit(checking ? OpCodes.Conv_Ovf_U4 : OpCodes.Conv_U4);
			else if (to == T.ULong)
				Emit(checking ? OpCodes.Conv_Ovf_U8 : OpCodes.Conv_U8);
			else if (to == T.Float)
				Emit(OpCodes.Conv_R4);
			else if (to == T.Double)
				Emit(OpCodes.Conv_R8);
			else
				Debug.Fail(String.Format("unknown cast from '{0}' to '{1}'", from.FullName, to.FullName));
		} else
			Debug.Fail(String.Format("unknown cast from '{0}' to '{1}'", from.FullName, to.FullName));
	}
	public virtual void EmitDefaultAccessor(Event e, Method m) {
		if (m.IsInstance) {
			this_access();	// for store, below
			this_access();
		}
		EmitLoad(e);
		Emit(OpCodes.Ldarg, m[0]);	// value
		binary_operator(m.Name.IndexOf("add") >= 0 ? "+" : "-", e.Type, null);
		EmitStore(e);
		Emit(OpCodes.Ret);
	}
	public virtual void EmitLoad(int index) {
		Emit(OpCodes.Ldloc, index);
	}
	public virtual void EmitLoad(Symbol f) {
		if (f is EnumMember)
			Emit(OpCodes.Ldc_I4, (int)((EnumMember)f).value);
		else if (f is Constant) {
			object value = ((Constant)f).value;
			if (value is double)
				Emit(OpCodes.Ldc_R8, (double)value);
			else if (value is float)
				Emit(OpCodes.Ldc_R4, (float)value);
			else if (value is string)
				Emit(OpCodes.Ldstr, (string)value);
			else if (value == null)
				Emit(OpCodes.Ldnull);
			else
				Emit(OpCodes.Ldc_I4, (int)value);
		} else if (f is Formal && ((Formal)f).modifier != null) {
			Emit(OpCodes.Ldarg, (Formal)f);
			EmitLoadIndirect(f.Type);
		} else if (f is Formal)
			Emit(OpCodes.Ldarg, (Formal)f);
		else if (f is Local)
			Emit(OpCodes.Ldloc, (Local)f);
		else if (f is Field && f.IsStatic)
			Emit(OpCodes.Ldsfld, (Field)f);
		else if (f is Field && f.IsInstance)
			Emit(OpCodes.Ldfld, (Field)f);
		else if (f is Property)
			EmitCall(((Property)f).Get);
		else if (f is Method)
			Emit(OpCodes.Ldftn, (Method)f);
	}
	public virtual void EmitLoadAddress(Symbol f) {
		if (f is Formal && ((Formal)f).modifier != null)
			Emit(OpCodes.Ldarg, (Formal)f);
		else if (f is Formal)
			Emit(OpCodes.Ldarga, (Formal)f);
		else if (f is Local)
			Emit(OpCodes.Ldloca, (Local)f);
		else if (f is Field && f.IsStatic)
			Emit(OpCodes.Ldsflda, (Field)f);
		else if (f is Field && f.IsInstance)
			Emit(OpCodes.Ldflda, (Field)f);
		else if (f is Property) {
			EmitCall(((Property)f).Get);
			int index = newLocal(f.Type);
			EmitStore(index);
			EmitLoadAddress(index);
		}
	}
	public virtual void EmitLoadAddress(int index) {
		Emit(OpCodes.Ldloca, index);
	}
	public virtual void EmitLoadElement(ArrayType ty) {
		Type ety = ty.elementType;
		if (ety.IsScalarType && ty.rank > 1)
			EmitLoadElement(ty, ety, ty.rank);
		else if (ety.IsScalarType) {
			if (ety is EnumType)
				ety = ((EnumType)ety).baseType;
			     if (ety == T.Bool)   Emit(OpCodes.Ldelem_I1);
			else if (ety == T.Byte)   Emit(OpCodes.Ldelem_U1);
			else if (ety == T.Char)   Emit(OpCodes.Ldelem_I2);
			else if (ety == T.Double) Emit(OpCodes.Ldelem_R8);
			else if (ety == T.Short)  Emit(OpCodes.Ldelem_I2);
			else if (ety == T.Int)    Emit(OpCodes.Ldelem_I4);
			else if (ety == T.Long)   Emit(OpCodes.Ldelem_I8);
			else if (ety == T.SByte)  Emit(OpCodes.Ldelem_I1);
			else if (ety == T.Float)  Emit(OpCodes.Ldelem_R4);
			else if (ety == T.String) Emit(OpCodes.Ldelem_Ref);
			else if (ety == T.UShort) Emit(OpCodes.Ldelem_U2);
			else if (ety == T.UInt)   Emit(OpCodes.Ldelem_U4);
			else if (ety == T.ULong)  Emit(OpCodes.Ldelem_I8);
			else if (ety is PointerType) Emit(OpCodes.Ldelem_U4);
			else Emit(OpCodes.Ldelem_Ref);
		} else {		// value types
			EmitLoadElementAddress(ty);
			EmitLoadIndirect(ety);
		}
	}
	abstract public void EmitLoadElement(ArrayType ty, Type ety, int rank);
	public virtual void EmitLoadElementAddress(ArrayType ty) {
		Type ety = ty.elementType;
		if (ty.rank == 1)
			Emit(OpCodes.Ldelema, ety);
		else
			EmitLoadElementAddress(ty, ety, ty.rank);
	}
	abstract public void EmitLoadElementAddress(ArrayType ty, Type ety, int rank);
	public virtual void EmitLoadIndirect(Type ty) {
		if (ty is EnumType)
			ty = ((EnumType)ty).baseType;
		if (!ty.IsScalarType)
			Emit(OpCodes.Ldobj, ty);
		else if (ty == T.Bool)   Emit(OpCodes.Ldind_I1);
		else if (ty == T.Byte)   Emit(OpCodes.Ldind_U1);
		else if (ty == T.Char)   Emit(OpCodes.Ldind_I2);
		else if (ty == T.Double) Emit(OpCodes.Ldind_R8);
		else if (ty == T.Short)  Emit(OpCodes.Ldind_I2);
		else if (ty == T.Int)    Emit(OpCodes.Ldind_I4);
		else if (ty == T.Long)   Emit(OpCodes.Ldind_I8);
		else if (ty == T.SByte)  Emit(OpCodes.Ldind_I1);
		else if (ty == T.Float)  Emit(OpCodes.Ldind_R4);
		else if (ty == T.String) Emit(OpCodes.Ldind_Ref);
		else if (ty == T.UShort) Emit(OpCodes.Ldind_U2);
		else if (ty == T.UInt)   Emit(OpCodes.Ldind_U4);
		else if (ty == T.ULong)  Emit(OpCodes.Ldind_I8);
		else if (ty is PointerType) Emit(OpCodes.Ldind_U4);
		else Emit(OpCodes.Ldind_Ref);
	}
	public virtual void EmitStore(int index) {
		Emit(OpCodes.Stloc, index);
	}
	public virtual void EmitStore(Symbol f) {
		if (f is Formal && ((Formal)f).modifier != null)
			EmitStoreIndirect(((Formal)f).Type);
		else if (f is Formal)
			Emit(OpCodes.Starg, (Formal)f);
		else if (f is Local)
			Emit(OpCodes.Stloc, (Local)f);
		else if (f is Field && f.IsStatic)
			Emit(OpCodes.Stsfld, (Field)f);
		else if (f is Field && f.IsInstance)
			Emit(OpCodes.Stfld, (Field)f);		
		else if (f is Property)
			EmitCall(((Property)f).Set);
	}
	abstract public void EmitStoreElement(ArrayType ty, Type ety, int rank);
	public virtual void EmitStoreElement(ArrayType ty, expression rhs) {
		Type ety = ty.elementType;
		if (ety.IsScalarType && ty.rank > 1) {
			expression(rhs);
			EmitStoreElement(ty, ety, ty.rank);
		} else if (ety.IsScalarType) {
			expression(rhs);
			if (ety is EnumType)
				ety = ((EnumType)ety).baseType;
			     if (ety == T.Bool)   Emit(OpCodes.Stelem_I1);
			else if (ety == T.Byte)   Emit(OpCodes.Stelem_I1);
			else if (ety == T.Char)   Emit(OpCodes.Stelem_I2);
			else if (ety == T.Double) Emit(OpCodes.Stelem_R8);
			else if (ety == T.Short)  Emit(OpCodes.Stelem_I2);
			else if (ety == T.Int)    Emit(OpCodes.Stelem_I4);
			else if (ety == T.Long)   Emit(OpCodes.Stelem_I8);
			else if (ety == T.SByte)  Emit(OpCodes.Stelem_I1);
			else if (ety == T.Float)  Emit(OpCodes.Stelem_R4);
			else if (ety == T.String) Emit(OpCodes.Stelem_Ref);
			else if (ety == T.UShort) Emit(OpCodes.Stelem_I2);
			else if (ety == T.UInt)   Emit(OpCodes.Stelem_I4);
			else if (ety == T.ULong)  Emit(OpCodes.Stelem_I8);
			else if (ety is PointerType) Emit(OpCodes.Stelem_I4);
			else Emit(OpCodes.Stelem_Ref);
		} else {	// value types
			EmitLoadElementAddress(ty);
			expression(rhs);
			EmitStoreIndirect(ety);
		}
	}
	public virtual void EmitStoreIndirect(Type ty) {
		if (ty is EnumType)
			ty = ((EnumType)ty).baseType;
		if (!ty.IsScalarType)
			Emit(OpCodes.Stobj, ty);
		else if (ty == T.Bool)   Emit(OpCodes.Stind_I1);
		else if (ty == T.Byte)   Emit(OpCodes.Stind_I1);
		else if (ty == T.Char)   Emit(OpCodes.Stind_I2);
		else if (ty == T.Double) Emit(OpCodes.Stind_R8);
		else if (ty == T.Short)  Emit(OpCodes.Stind_I2);
		else if (ty == T.Int)    Emit(OpCodes.Stind_I4);
		else if (ty == T.Long)   Emit(OpCodes.Stind_I8);
		else if (ty == T.SByte)  Emit(OpCodes.Stind_I1);
		else if (ty == T.Float)  Emit(OpCodes.Stind_R4);
		else if (ty == T.String) Emit(OpCodes.Stind_Ref);
		else if (ty == T.UShort) Emit(OpCodes.Stind_I2);
		else if (ty == T.UInt)   Emit(OpCodes.Stind_I4);
		else if (ty == T.ULong)  Emit(OpCodes.Stind_I8);
		else if (ty is PointerType) Emit(OpCodes.Stind_I4);
		else Emit(OpCodes.Stind_Ref);
	}
	abstract public void EmitSwitch(int[] caselabels);
	public virtual void empty_statement(empty_statement ast) {}
	public virtual void EndTry(object handle) {	defLabel((int)handle); }
	public virtual void expr_access(expr_access ast, bool lvalue) {
		if (ast.sym is Type)
			return;
		expression(ast.expr, ast.expr.typ.IsValueType);
		if (ast.sym is Property && ast.sym.Name == "Length"
		&& ast.expr.typ is ArrayType && ((ArrayType)ast.expr.typ).rank == 1) {
			Emit(OpCodes.Ldlen);
			EmitCast(T.UInt, T.Int);
		} else if (lvalue)
			EmitLoadAddress(ast.sym);
		else if (ast.sym is Property && ast.expr is base_access)
			EmitCall(OpCodes.Call, ((Property)ast.sym).Get);
		else
			EmitLoad(ast.sym);
	}
	public virtual void expr_access(expr_access ast, expression rhs) {
		if (ast.sym is Type)
			return;
		expression(ast.expr, ast.expr.typ.IsValueType);
		expression(rhs);
		if (ast.sym is Property && ast.expr is base_access)
			EmitCall(OpCodes.Call, ((Property)ast.sym).Set);
		else
			EmitStore(ast.sym);
	}
	public virtual void expr_initializer(expr_initializer ast) {
		expression(ast.expr);
	}
	public virtual void expression(expression ast) {
		asts.Push(ast);
		     if (ast is array_creation_expression1) array_creation_expression1((array_creation_expression1)ast);
		else if (ast is array_creation_expression2) array_creation_expression2((array_creation_expression2)ast);
		else if (ast is as_expression) as_expression((as_expression)ast);
		else if (ast is assignment_expression) assignment_expression((assignment_expression)ast);
		else if (ast is base_access) base_access((base_access)ast);
		else if (ast is binary_expression) binary_expression((binary_expression)ast, 0, 0);
		else if (ast is literal) literal((literal)ast);
		else if (ast is cast_expression) cast_expression((cast_expression)ast);
		else if (ast is checked_expression) checked_expression((checked_expression)ast, false);
		else if (ast is compound_assignment_expression) compound_assignment_expression((compound_assignment_expression)ast);
		else if (ast is cond_expression) cond_expression((cond_expression)ast);
		else if (ast is element_access) element_access((element_access)ast, false);
		else if (ast is member_access) member_access((member_access)ast, false);
		else if (ast is implicit_cast_expression) implicit_cast_expression((implicit_cast_expression)ast);
		else if (ast is invocation_expression) invocation_expression((invocation_expression)ast);
		else if (ast is is_expression) is_expression((is_expression)ast);
		else if (ast is local_expression) local_expression((local_expression)ast, false);
		else if (ast is new_expression) new_expression((new_expression)ast);
		else if (ast is post_expression) post_expression((post_expression)ast);
		else if (ast is pre_expression) pre_expression((pre_expression)ast);
		else if (ast is simple_name) simple_name((simple_name)ast, false);
		else if (ast is sizeof_expression) sizeof_expression((sizeof_expression)ast);
		else if (ast is temporary) temporary((temporary)ast);
		else if (ast is this_access) this_access();
		else if (ast is typeof_expression) typeof_expression((typeof_expression)ast);
		else if (ast is unary_expression) unary_expression((unary_expression)ast, 0, 0);
		else if (ast is unchecked_expression) unchecked_expression((unchecked_expression)ast, false);
		else throw new ArgumentException();
		asts.Pop();
	}
	public virtual void expression(expression ast, int trueLabel, int falseLabel) {
		if (ast is binary_expression)
			binary_expression((binary_expression)ast, trueLabel, falseLabel);
		else if (ast is unary_expression)
			unary_expression((unary_expression)ast, trueLabel, falseLabel);
		else {
			expression(ast);
			if (trueLabel != 0)
				gotoLabel(OpCodes.Brtrue, trueLabel);
			if (falseLabel != 0)
				gotoLabel(OpCodes.Brfalse, falseLabel);
		}
	}
	public virtual void expression(expression ast, bool lvalue) {
		asts.Push(ast);
		     if (ast is checked_expression) checked_expression((checked_expression)ast, lvalue);
		else if (ast is element_access) element_access((element_access)ast, lvalue);
		else if (ast is member_access) member_access((member_access)ast, lvalue);
		else if (ast is local_expression) local_expression((local_expression)ast, lvalue);
		else if (ast is simple_name) simple_name((simple_name)ast, lvalue);
		else if (ast is unchecked_expression) unchecked_expression((unchecked_expression)ast, lvalue);
		else expression(ast);
		asts.Pop();
	}
	public virtual void expression(expression ast, expression rhs) {
		asts.Push(ast);
		     if (ast is checked_expression) checked_expression((checked_expression)ast, rhs);
		else if (ast is element_access) element_access((element_access)ast, rhs);
		else if (ast is member_access) member_access((member_access)ast, rhs);
		else if (ast is local_expression) local_expression((local_expression)ast, rhs);
		else if (ast is simple_name) simple_name((simple_name)ast, rhs);
		else if (ast is unchecked_expression) unchecked_expression((unchecked_expression)ast, rhs);
		else Debug.Fail(String.Format("unknown assignment '{0}'", ast));
		asts.Pop();
	}
	public virtual void expression_statement(expression_statement ast) {
		expression(ast.expr);
	}
	public virtual int genLabel(int n) {
		nextlab += n;
		return nextlab - n;
	}
	public virtual void fixed_statement(fixed_statement ast) {
		msg.Error("fixed statement not implemented");
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
		ast.lab = genLabel(4);
		if (ast.init != null)
			for_init(ast.init);
		gotoLabel(ast.lab + 3);
		defLabel(ast.lab);
		statement(ast.body);
		defLabel(ast.lab + 1);
		foreach (expression x in ast.iterators)
			expression(x);
		defLabel(ast.lab + 3);
		if (ast.cond != null)
			expression(ast.cond, ast.lab, 0);
		else
			gotoLabel(ast.lab);
		defLabel(ast.lab + 2);
	}
	public virtual void foreach_array(foreach_statement ast) {
	//
	//foreach (T x in array) S
	//=>
	//for (int i = 0; i < array.Length; ++i) {
	//	 x = (T)array[i];
	//	 S
	//}
	// 
		int index = newLocal(T.Int), array = newLocal(ast.expr.typ);
		expression(ast.expr);
		EmitStore(array);
		Emit(OpCodes.Ldc_I4_0);
		EmitStore(index);
		gotoLabel(ast.lab + 3);
		defLabel(ast.lab);
		EmitLoad(array);
		EmitLoad(index);
		EmitLoadElement((ArrayType)ast.expr.typ);
		EmitCast(((ArrayType)ast.expr.typ).elementType, ast.sym.Type);
		EmitStore(ast.sym);
		statement(ast.body);
		defLabel(ast.lab + 1);
		EmitLoad(index);
		Emit(OpCodes.Ldc_I4_1);
		Emit(OpCodes.Add);
		EmitStore(index);
		defLabel(ast.lab + 3);
		EmitLoad(index);
		EmitLoad(array);
		Emit(OpCodes.Ldlen);
		EmitCast(T.UInt, T.Int);
		gotoLabel(OpCodes.Blt, ast.lab);
		defLabel(ast.lab + 2);
	}
	public virtual void foreach_withTry(foreach_statement ast, int enumerator) {
		//
		//try {
		//	 foreach_body expansion...
		//} finally {
		//	 IDisposable disposable = enumerator as System.IDisposable;
		//	 if (disposable != null) disposable.Dispose();
		//}
		// 
		object handle = BeginTry();
		foreach_body(ast, enumerator);
		handle = BeginFinally(handle);
		EmitLoad(enumerator);
		if (ast.GetEnumerator.Type.Implements(T.IDisposable)) {
			EmitCast(ast.GetEnumerator.Type, T.IDisposable);
			EmitCall(T.IDisposable.FindMethod("Dispose"));
		} else {
			int disposable = newLocal(T.IDisposable);
			Emit(OpCodes.Isinst, T.IDisposable);
			EmitStore(disposable);
			EmitLoad(disposable);
			int lab = genLabel(1);
			gotoLabel(OpCodes.Brfalse, lab);
			EmitLoad(disposable);
			EmitCall(T.IDisposable.FindMethod("Dispose"));
			defLabel(lab);
		}
		EndTry(handle);
		defLabel(ast.lab + 3);
	}
	public virtual void foreach_body(foreach_statement ast, int enumerator) {
	//
	//foreach (T x in collection) S
	//=>
	//while (enumerator.MoveNext()) {
	//	T element = (T)enumerator.Current;
	//	S
	//}
	// 
		gotoLabel(ast.lab + 1);
		defLabel(ast.lab);
		EmitLoad(enumerator);
		EmitLoad(ast.Current);
		EmitCast(ast.Current.Type, ast.sym.Type);
		EmitStore(ast.sym);
		statement(ast.body);
		defLabel(ast.lab + 1);
		EmitLoad(enumerator);
		EmitCall(ast.MoveNext);
		gotoLabel(OpCodes.Brtrue, ast.lab);
		defLabel(ast.lab + 2);
	}
	public virtual void foreach_statement(foreach_statement ast) {
		ast.lab = genLabel(4);
		ast.sym.ordinal = newLocal(ast.sym.Type);
		if (ast.expr.typ is ArrayType && ((ArrayType)ast.expr.typ).rank == 1)
			foreach_array(ast);
		else {
			//
			//E enumerator = (collection).GetEnumerator();
			//or
			//IEnumerator enumerator = ((System.Collections.IEnumerable)(collection)).GetEnumerator();
			//
			int enumerator = newLocal(ast.GetEnumerator.Type);
			expression(ast.expr);
			EmitCall(ast.GetEnumerator);
			EmitStore(enumerator);
			if (ast.GetEnumerator.Type.Implements(T.IDisposable)
			|| !ast.GetEnumerator.Type.Is("sealed"))
				foreach_withTry(ast, enumerator);
			else
				foreach_body(ast, enumerator);
		}
	}
	public virtual void goto_case_statement(goto_case_statement ast) {
		if (ast.label != null)
			gotoLabel(ast.exitstry ? OpCodes.Leave : OpCodes.Br, ((switch_section)ast.label.parent).lab);
	}
	public virtual void goto_default_statement(goto_default_statement ast) {
		if (ast.stmt != null)
			gotoLabel(ast.exitstry ? OpCodes.Leave : OpCodes.Br, ast.stmt.lab);
	}
	public virtual void goto_statement(goto_statement ast) {
		if (ast.target.lab == 0)
			ast.target.lab = genLabel(1);
		ast.lab = ast.target.lab;
		gotoLabel(ast.exitstry ? OpCodes.Leave : OpCodes.Br, ast.lab);
	}
	abstract public void gotoLabel(OpCode inst, int lab);
	public void gotoLabel(int lab) {
		gotoLabel(OpCodes.Br, lab);
	}
	public virtual void if_statement(if_statement ast) {
		ast.lab = genLabel(2);
		expression(ast.expr, 0, ast.lab);
		statement(ast.thenpart);
		if (ast.elsepart != null) {
			gotoLabel(ast.lab + 1);
			defLabel(ast.lab);
			statement(ast.elsepart);
		} else
			defLabel(ast.lab);
		defLabel(ast.lab + 1);
	}
	public virtual void implicit_cast_expression(implicit_cast_expression ast) {
		expression(ast.expr);
		EmitCast(ast.expr.typ, ast.typ);
	}
	public virtual void integer_literal(integer_literal ast) {
		if (ast.typ == T.Long || ast.typ == T.ULong)
			Emit(OpCodes.Ldc_I8, (long)ast.value);
		else
			Emit(OpCodes.Ldc_I4, (int)ast.value);
	}
	public virtual void invocation_expression(invocation_expression ast) {
		if (ast.method.IsInstance) {
			expression(ast.expr);
			if (ast.expr.typ.IsValueType && ast.method.GetType().IsReferenceType)
				Emit(OpCodes.Box, ast.expr.typ);
		}
		EmitArgumentList(ast.method, ast.args);
		if (ast.expr is expr_access && ((expr_access)ast.expr).expr is base_access)
			EmitCall(OpCodes.Call, ast.method);
		else
			EmitCall(ast.method);
		if (ast.typ != T.Void && !ast.valueUsed)
			Emit(OpCodes.Pop);
	}
	public static bool is_event_access(expression ast) {
		Event e = null;
		if (ast is simple_name)
			e = ((simple_name)ast).sym as Event;
		else if (ast is member_access)
			e = ((member_access)ast).sym as Event;
		if (e == null)
			return false;
		if (e.GetType() != currentClass(ast))
			return true;
		return !e.IsFieldLike;
	}
	public virtual void is_expression(is_expression ast) {
		expression(ast.expr);
		Emit(OpCodes.Isinst, ast.sym);
	}
	public virtual void labeled_statement(labeled_statement ast) {
		if (ast.lab == 0)
			ast.lab = genLabel(1);
		defLabel(ast.lab);
		statement(ast.stmt);
	}
	public virtual void literal(literal ast) {
		if (ast is boolean_literal) boolean_literal((boolean_literal)ast);
		else if (ast is character_literal) character_literal((character_literal)ast);
		else if (ast is integer_literal) integer_literal((integer_literal)ast);
		else if (ast is null_literal) null_literal((null_literal)ast);
		else if (ast is real_literal) real_literal((real_literal)ast);
		else if (ast is string_literal) string_literal((string_literal)ast);
		else throw new ArgumentException();
	}
	public virtual void local_expression(local_expression ast, bool lvalue) {
		if (ast.value != null) {
			expression(ast.value, lvalue);
			return;
		}
		expression(ast.expr, lvalue);
		if (ast.expr is assignment_expression)
			ast.value = ((assignment_expression)ast.expr).e2;
		else if (ast.expr is local_expression)
			ast.value = ((local_expression)ast.expr).value;
		else {
			int temp = newLocal(ast.expr.typ);
			Emit(OpCodes.Dup);
			EmitStore(temp);
			ast.value = new temporary(ast.expr.typ, temp);
		}
	}
	public virtual void local_expression(local_expression ast, expression rhs) {
		expression(ast.expr, rhs);
	}
	public virtual void local_statement(local_statement ast) {
		foreach (var_declarator x in ast.vars)
			x.sym.ordinal = newLocal(x.sym);
		foreach (var_declarator x in ast.vars)
			if (x.init != null) {
				variable_initializer(x.init);
				EmitStore(x.sym);
			}
	}
	public virtual void lock_statement(lock_statement ast) {
		int var = newLocal(ast.expr.typ);
		expression(ast.expr);
		Emit(OpCodes.Dup);
		EmitStore(var);
		System.Type monitor = System.Type.GetType("System.Threading.Monitor");
		// try {
			object handle = BeginTry();
			EmitCall(T.Monitor.FindMethod("Enter", T.Object));
			statement(ast.body);
		// } finally {
			handle = BeginFinally(handle);
			EmitLoad(var);
			EmitCall(T.Monitor.FindMethod("Exit", T.Object));
		// }
		EndTry(handle);
	}
	public virtual void member_access(member_access ast, bool lvalue) {
		     if (ast is expr_access) expr_access((expr_access)ast, lvalue);
		else if (ast is pointer_access) pointer_access((pointer_access)ast, lvalue);
		else if (ast is predefined_access) predefined_access((predefined_access)ast, lvalue);
		else throw new ArgumentException();
	}
	public virtual void member_access(member_access ast, expression rhs) {
		if (ast is expr_access) expr_access((expr_access)ast, rhs);
		else if (ast is pointer_access) pointer_access((pointer_access)ast, rhs);
		else if (ast is predefined_access) predefined_access((predefined_access)ast, rhs);
		else throw new ArgumentException();
	}
	public virtual void new_expression(new_expression ast) {
		if (ast.typ == T.Long || ast.typ == T.ULong)
			Emit(OpCodes.Ldc_I8, 0L);
		else if (ast.typ.IsSigned || ast.typ.IsUnsigned || ast.typ == T.Char
		|| ast.typ == T.Bool || ast.typ is EnumType)
			Emit(OpCodes.Ldc_I4_0);
		else if (ast.typ == T.Double)
			Emit(OpCodes.Ldc_R8, 0.0d);
		else if (ast.typ == T.Float)
			Emit(OpCodes.Ldc_R4, 0.0f);
		else if (ast.typ.IsValueType) {
			int var = newLocal(ast.typ);
			EmitLoadAddress(var);
			if (ast.args.Count == 0)
				Emit(OpCodes.Initobj, ast.typ);
			else {
				EmitArgumentList(ast.method, ast.args);
				EmitCall(ast.method);
			}
			EmitLoad(var);
		} else if (ast.typ is DelegateType) {
			expression e = ast.args[0].expr;
			if (e.typ is DelegateType) {
				expression(e);
				EmitLoad(((DelegateType)ast.typ).invoke);
			} else {
				Method m;
				if (e is simple_name)
					m = (Method)((simple_name)e).sym;
				else
					m = (Method)((member_access)e).sym;
				if (m.IsInstance)
					expression(e);
				else {
					Emit(OpCodes.Ldnull);
					EmitLoad(m);
				}
			}
			Emit(OpCodes.Newobj, ast.method);
		} else {
			EmitArgumentList(ast.args);
			Emit(OpCodes.Newobj, ast.method);
		}
	}
	abstract public int newLocal(Type ty);
	public virtual int newLocal(Local v) {
		v.ordinal = newLocal(v.Type);
		return v.ordinal;
	}
	public virtual int newLocal(Type ty, string name) {
		return newLocal(ty);
	}
	public virtual void null_literal(null_literal ast) {
		Emit(OpCodes.Ldnull);
	}
	public virtual void pointer_access(pointer_access ast, bool lvalue) {
		msg.Error("pointer access not implemented");
	}
	public virtual void pointer_access(pointer_access ast, expression rhs) {
		msg.Error("pointer access not implemented");
	}
	public virtual void post_expression(post_expression ast) {
		if (ast.method != null && ast.method.declSpace != null) {
			expression(ast.expr);
			if (ast.valueUsed)
				Emit(OpCodes.Dup);
			EmitCall(ast.method);
			Emit(OpCodes.Pop);
		} else {
			expression(ast.expr);
			if (ast.valueUsed)
				Emit(OpCodes.Dup);
			Emit(OpCodes.Ldc_I4_1);
			binary_operator(ast.op.str.Substring(0, 1), ast.typ, ast.method);
			temporary rhs = new temporary(ast.typ, newLocal(ast.typ));
			EmitStore(rhs.var);
			expression(ast.expr, rhs);
		}
	}
	public virtual void pre_expression(pre_expression ast) {
		if (ast.method != null && ast.method.declSpace != null) {
			expression(ast.expr);
			EmitCall(ast.method);
			if (!ast.valueUsed)
				Emit(OpCodes.Pop);
		} else {
			expression(ast.expr);
			Emit(OpCodes.Ldc_I4_1);
			binary_operator(ast.op.str.Substring(0, 1), ast.typ, ast.method);
			temporary rhs = new temporary(ast.typ, newLocal(ast.typ));
			EmitStore(rhs.var);
			expression(ast.expr, rhs);
			if (ast.valueUsed)
				expression(rhs);
		}
	}
	public virtual void predefined_access(predefined_access ast, bool lvalue) {
		if (ast.sym != null)
			EmitLoad(ast.sym);
	}
	public virtual void predefined_access(predefined_access ast, expression rhs) {
		if (ast.sym != null) {
			expression(rhs);
			EmitStore(ast.sym);
		}
	}
	public virtual void real_literal(real_literal ast) {
		if (ast.typ == T.Double)
			Emit(OpCodes.Ldc_R8, (double)ast.value);
		else
			Emit(OpCodes.Ldc_R4, (float)ast.value);
	}
	public virtual void resource_decl(resource_decl ast, using_statement stmt) {
		foreach (var_declarator v in ast.local.vars) {
			v.sym.ordinal = newLocal(v.sym.Type, v.sym.Name);
			if (v.init != null) {
				expression(((expr_initializer)v.init).expr);
				EmitStore(v.sym);
			}
		}
		object handle = BeginTry();
		// try {
			statement(stmt.body);
		// } finally {
			handle = BeginFinally(handle);
			for (int i = ast.local.vars.Count - 1; i >= 0; i--) {
				var_declarator v = (var_declarator)ast.local.vars[i];
				int lab = 0;
				if (ast.local.ty.sym.IsReferenceType) {
					lab = genLabel(1);
					EmitLoad(v.sym);
					gotoLabel(OpCodes.Brfalse /* brnull */, lab);
					EmitLoad(v.sym);
				} else
					EmitLoadAddress(v.sym);
				if (ast.method != null)
					EmitCall(ast.method);
				EmitCall(ast.dispose);
				if (lab != 0)
					defLabel(lab);
			}
		// }
			EndTry(handle);
	}
	public virtual void resource_expr(resource_expr ast, using_statement stmt) {
		int var = newLocal(ast.expr.typ);
		expression(ast.expr);
		EmitStore(var);
		object handle = BeginTry();
		// try {
			statement(stmt.body);
		// } finally {
			handle = BeginFinally(handle);
			int lab = 0;
			if (ast.expr.typ.IsReferenceType) {
				lab = genLabel(1);
				EmitLoad(var);
				gotoLabel(OpCodes.Brfalse /* brnull */, lab);
				EmitLoad(var);
			} else
				EmitLoadAddress(var);
			EmitCall(ast.dispose);
			if (lab != 0)
				defLabel(lab);
		// }
		EndTry(handle);
	}
	public virtual void return_statement(return_statement ast) {
		if (ast.expr != null) {
			expression(ast.expr);
			EmitStore(retvar);
			gotoLabel(ast.exitstry ? OpCodes.Leave : OpCodes.Br, retlab);
		} else
			Emit(OpCodes.Ret);
	}
	public virtual void simple_name(simple_name ast, bool lvalue) {
		if (ast.sym == null || ast.sym is Type)
			return;
		if (ast.sym.IsInstance)
			this_access();
		if (lvalue)
			EmitLoadAddress(ast.sym);
		else
			EmitLoad(ast.sym);
	}
	public virtual void simple_name(simple_name ast, expression rhs) {
		if (ast.sym == null || ast.sym is Type)
			return;
		if (ast.sym.IsInstance)
			this_access();
		else if (ast.sym is Formal && ((Formal)ast.sym).modifier != null)
			EmitLoadAddress(ast.sym);
		expression(rhs);
		EmitStore(ast.sym);
	}
	public virtual void sizeof_expression(sizeof_expression ast) {
		Emit(OpCodes.Sizeof, ast.ty.sym);
	}
	public virtual void stackalloc_initializer(stackalloc_initializer ast) {
		Emit(OpCodes.Sizeof, ast.ty.sym);
		expression(ast.expr);
		Emit(OpCodes.Mul);
		Emit(OpCodes.Localloc);
	}
	public virtual void statement(statement ast) {
		asts.Push(ast);
		     if (ast is block_statement) block_statement((block_statement)ast);
		else if (ast is break_statement) break_statement((break_statement)ast);
		else if (ast is checked_statement) checked_statement((checked_statement)ast);
		else if (ast is const_statement) const_statement((const_statement)ast);
		else if (ast is continue_statement) continue_statement((continue_statement)ast);
		else if (ast is do_statement) do_statement((do_statement)ast);
		else if (ast is empty_statement) empty_statement((empty_statement)ast);
		else if (ast is expression_statement) expression_statement((expression_statement)ast);
		else if (ast is fixed_statement) fixed_statement((fixed_statement)ast);
		else if (ast is for_statement) for_statement((for_statement)ast);
		else if (ast is foreach_statement) foreach_statement((foreach_statement)ast);
		else if (ast is goto_case_statement) goto_case_statement((goto_case_statement)ast);
		else if (ast is goto_default_statement) goto_default_statement((goto_default_statement)ast);
		else if (ast is goto_statement) goto_statement((goto_statement)ast);
		else if (ast is if_statement) if_statement((if_statement)ast);
		else if (ast is labeled_statement) labeled_statement((labeled_statement)ast);
		else if (ast is local_statement) local_statement((local_statement)ast);
		else if (ast is lock_statement) lock_statement((lock_statement)ast);
		else if (ast is return_statement) return_statement((return_statement)ast);
		else if (ast is switch_statement) switch_statement((switch_statement)ast);
		else if (ast is throw_statement) throw_statement((throw_statement)ast);
		else if (ast is try_statement) try_statement((try_statement)ast);
		else if (ast is unchecked_statement) unchecked_statement((unchecked_statement)ast);
		else if (ast is unsafe_statement) statement(((unsafe_statement)ast).block);
		else if (ast is using_statement) using_statement((using_statement)ast);
		else if (ast is while_statement) while_statement((while_statement)ast);
		else throw new ArgumentException();
		asts.Pop();
	}
	public virtual void statement(statement ast, Method m) {
		if (m.Type != T.Void) {
			retlab = ast.lab = genLabel(1);
			retvar = newLocal(m.Type);
		}
		statement(ast);
		if (m.Type != T.Void) {
			defLabel(retlab);
			EmitLoad(retvar);
		}
		Emit(OpCodes.Ret);
	}
	public virtual void string_literal(string_literal ast) {
		Emit(OpCodes.Ldstr, (string)ast.value);
	}
	public virtual void switch_search(switch_expressionList values, int lb, int ub, int temp) {
		for (int i = lb; i <= ub; i++) {
			EmitLoad(temp);
			if (values[i].expr is string_literal)
				string_literal((string_literal)values[i].expr);
			else
				Emit(OpCodes.Ldc_I4, (int)(uint)values[i].expr.value);
			gotoLabel(OpCodes.Beq, ((switch_section)values[i].parent).lab);
		}
	}
	public virtual void switch_section(switch_section ast) {
		asts.Push(ast);
		defLabel(ast.lab);
		foreach (statement x in ast.stmts)
			statement(x);
		asts.Pop();
	}
	public virtual void switch_section(switch_section ast, int dlab, ref bool hasdefault) {
		foreach (switch_label x in ast.labels)
			if (x is switch_default) {
				hasdefault = true;
				ast.lab = dlab;
				return;
			}
		ast.lab = genLabel(1);
	}
	public virtual void switch_statement(switch_statement ast) {
		ast.lab = genLabel(3);
		bool hasdefault = false;
		foreach (switch_section s in ast.sections)
			switch_section(s, ast.lab, ref hasdefault);
		expression(ast.expr);
		int temp = newLocal(ast.typ);
		EmitStore(temp);
		if (ast.typ == T.String) {
			EmitLoad(temp);
			gotoLabel(OpCodes.Brfalse, ast.lab);
			EmitLoad(temp);
			EmitCall(T.String.FindMethod("Intern", T.String));
			EmitStore(temp);
			switch_search(ast.values, 0, ast.values.Count - 1, temp);
			gotoLabel(ast.lab);
		} else if (ast.typ == T.Long || ast.typ == T.ULong) {
			switch_search(ast.values, 0, ast.values.Count - 1, temp);
			gotoLabel(ast.lab);
		} else if (ast.values.Count > 0) {
			int i, j;
			for (i = 0; i < ast.values.Count; i = j) {
				for (j = i + 1; j < ast.values.Count; j++)
					if (((uint)ast.values[j].expr.value - (uint)ast.values[i].expr.value + 1)/(j - i + 1) > 2)
						break;
				if (j - i < 2)
					switch_search(ast.values, i, j - 1, temp);
				else
					switch_table(ast.values, i, j - 1, temp, ast.lab);
			}
			gotoLabel(ast.lab);
		}
		foreach (switch_section s in ast.sections)
			switch_section(s);
		if (!hasdefault)
			defLabel(ast.lab);
		defLabel(ast.lab + 1);
		defLabel(ast.lab + 2);
	}
	public virtual void switch_table(switch_expressionList values, int lb, int ub, int temp, int dlab) {
		EmitLoad(temp);
		uint n = (uint)values[lb].expr.value;
		if (n > 0) {
			Emit(OpCodes.Ldc_I4, (int)n);
			Emit(OpCodes.Sub);
		}
		int[] labels = new int[(uint)values[ub].expr.value-n+1];
		int j = 0;
		for (int i = lb; i <= ub; i++) {
			for ( ; n < (uint)values[i].expr.value; n++)
				labels[j++] = dlab;
			labels[j++] = ((switch_section)values[i].parent).lab;
			n++;
		}
		Debug.Assert(j == labels.Length);
		EmitSwitch(labels);
	}
	public virtual void temporary(temporary ast) {
		EmitLoad(ast.var);
	}
	public virtual void this_access() {
		Emit(OpCodes.Ldarg_0);
	}
	public virtual void this_initializer(this_initializer ast) {
		this_access();
		EmitArgumentList(ast.method, ast.args);
		EmitCall(ast.method);
	}
	public virtual void throw_statement(throw_statement ast) {
		if (ast.expr != null) {
			expression(ast.expr);
			Emit(OpCodes.Throw);
		} else
			Emit(OpCodes.Rethrow);
	}
	public virtual void try_statement(try_statement ast) {
		object handle1 = null, handle2 = null;
		ast.lab = genLabel(1);
		if (ast.finally_block != null)
			handle1 = BeginTry();
		if (ast.catches != null)
			handle2 = BeginTry();
		statement(ast.block);
		if (ast.catches != null) {
			catch_clauses(ast.catches, handle2);
			EndTry(handle2);
		}
		if (ast.finally_block != null) {
			handle1 = BeginFinally(handle1);
			statement(ast.finally_block.block);
			EndTry(handle1);
		}
		defLabel(ast.lab);
	}
	public virtual void typeof_expression(typeof_expression ast) {
		Emit(OpCodes.Ldtoken, ast.ty.sym);
		EmitCall(T.Type.FindMethod("GetTypeFromHandle", T.RuntimeTypeHandle));
	}
	public virtual void unary_expression(unary_expression ast, int trueLabel, int falseLabel) {
		switch (ast.op.str) {
		case "!":
			if (trueLabel != 0 || falseLabel != 0)
				expression(ast.expr, falseLabel, trueLabel);
			else {
				expression(ast.expr);
				Emit(OpCodes.Ldc_I4_1);
				Emit(OpCodes.Xor);
			}
			return;
		}
		switch (ast.op.str) {
		case "-":
			if (checking && (ast.typ.IsSigned || ast.typ.IsUnsigned)) {
				Emit(OpCodes.Ldc_I4_0);
				expression(ast.expr);
				if (ast.expr.typ.IsUnsigned)
					Emit(OpCodes.Sub_Ovf_Un);
				else
					Emit(OpCodes.Sub_Ovf);
				break;
			}
			expression(ast.expr);
			Emit(OpCodes.Neg);
			break;
		case "+": expression(ast.expr);	break;
		case "~": expression(ast.expr); Emit(OpCodes.Not); break;
		case "*": msg.Error("indirection not implemented"); break;
		}
	}
	public virtual void unchecked_expression(unchecked_expression ast, bool lvalue) {
		bool save = checking;
		checking = true;
		expression(ast.expr, lvalue);
		checking = save;
	}
	public virtual void unchecked_expression(unchecked_expression ast, expression rhs) {
		bool save = checking;
		checking = true;
		expression(ast.expr, rhs);
		checking = save;
	}
	public virtual void unchecked_statement(unchecked_statement ast) {
		bool save = checking;
		checking = true;
		statement(ast.stmt);
		checking = save;
	}
	public virtual void using_statement(using_statement ast) {
		ast.lab = genLabel(1);
		if (ast.r is resource_expr)
			resource_expr((resource_expr)ast.r, ast);
		else
			resource_decl((resource_decl)ast.r, ast);
		defLabel(ast.lab);
	}
	public virtual void variable_initializer(variable_initializer ast) {
		     if (ast is array_initializer) array_initializer((array_initializer)ast);
		else if (ast is expr_initializer) expr_initializer((expr_initializer)ast);
		else if (ast is stackalloc_initializer) stackalloc_initializer((stackalloc_initializer)ast);
		else throw new ArgumentException();
	}
	public virtual void while_statement(while_statement ast) {
		ast.lab = genLabel(3);
		gotoLabel(ast.lab + 1);
		defLabel(ast.lab);
		statement(ast.body);
		defLabel(ast.lab + 1);
		expression(ast.expr, ast.lab, 0);
		defLabel(ast.lab + 2);
	}
}
