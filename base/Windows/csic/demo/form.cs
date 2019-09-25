using System;
using System.IO;
using System.Drawing;
using System.Collections;
using System.ComponentModel;
using System.Windows.Forms;
using System.Reflection;
using System.Reflection.Emit;

	/// <summary>
	/// Summary description for Form.
	/// </summary>
	public class Form1 : System.Windows.Forms.Form {
		private System.Windows.Forms.MainMenu mainMenu1;
		private System.Windows.Forms.MenuItem menuItem1;
		private System.Windows.Forms.MenuItem menuItem3;
		private System.Windows.Forms.TextBox textBox1;
		private System.Windows.Forms.MenuItem menuItem4;
		private System.Windows.Forms.OpenFileDialog openFileDialog1;
		private System.Windows.Forms.ContextMenu contextMenu1;
		private System.Windows.Forms.MenuItem menuItem2;
		private System.Windows.Forms.MenuItem menuItem5;
		private System.Windows.Forms.MenuItem menuItem6;
		private System.Windows.Forms.SaveFileDialog saveFileDialog1;
		private System.Windows.Forms.MenuItem menuItem7;
		public System.Windows.Forms.ListBox listBox1;
		private System.Windows.Forms.Label label1;
		private System.Windows.Forms.RichTextBox richTextBox1;
		private System.Windows.Forms.ListBox listBox2;
		/// <summary>
		/// Required designer variable.
		/// </summary>
		private System.ComponentModel.Container components = null;

		public Form1() {
			//
			// Required for Windows Form Designer support
			//
			InitializeComponent();
			//
			// TODO: Add any constructor code after InitializeComponent call
			//
			StringWriter w = new ListBoxWriter(listBox2);
			Console.SetError(w);
			Console.SetOut(w);
		}

		/// <summary>
		/// Clean up any resources being used.
		/// </summary>
		protected override void Dispose( bool disposing ) {
			if( disposing ) {
				if(components != null) {
					components.Dispose();
				}
			}
			base.Dispose( disposing );
		}

		#region Windows Form Designer generated code
		/// <summary>
		/// Required method for Designer support - do not modify
		/// the contents of this method with the code editor.
		/// </summary>
		private void InitializeComponent() {
			this.mainMenu1 = new System.Windows.Forms.MainMenu();
			this.menuItem1 = new System.Windows.Forms.MenuItem();
			this.menuItem4 = new System.Windows.Forms.MenuItem();
			this.menuItem6 = new System.Windows.Forms.MenuItem();
			this.menuItem7 = new System.Windows.Forms.MenuItem();
			this.menuItem3 = new System.Windows.Forms.MenuItem();
			this.menuItem2 = new System.Windows.Forms.MenuItem();
			this.menuItem5 = new System.Windows.Forms.MenuItem();
			this.textBox1 = new System.Windows.Forms.TextBox();
			this.openFileDialog1 = new System.Windows.Forms.OpenFileDialog();
			this.contextMenu1 = new System.Windows.Forms.ContextMenu();
			this.saveFileDialog1 = new System.Windows.Forms.SaveFileDialog();
			this.listBox1 = new System.Windows.Forms.ListBox();
			this.label1 = new System.Windows.Forms.Label();
			this.richTextBox1 = new System.Windows.Forms.RichTextBox();
			this.listBox2 = new System.Windows.Forms.ListBox();
			this.SuspendLayout();
			// 
			// mainMenu1
			// 
			this.mainMenu1.MenuItems.AddRange(new System.Windows.Forms.MenuItem[] {
																					  this.menuItem1,
																					  this.menuItem2,
																					  this.menuItem5});
			// 
			// menuItem1
			// 
			this.menuItem1.Index = 0;
			this.menuItem1.MenuItems.AddRange(new System.Windows.Forms.MenuItem[] {
																					  this.menuItem4,
																					  this.menuItem6,
																					  this.menuItem7,
																					  this.menuItem3});
			this.menuItem1.Text = "File";
			// 
			// menuItem4
			// 
			this.menuItem4.Index = 0;
			this.menuItem4.Text = "Load";
			this.menuItem4.Click += new System.EventHandler(this.onLoad);
			// 
			// menuItem6
			// 
			this.menuItem6.Index = 1;
			this.menuItem6.Text = "Save As";
			this.menuItem6.Click += new System.EventHandler(this.onSaveAs);
			// 
			// menuItem7
			// 
			this.menuItem7.Enabled = false;
			this.menuItem7.Index = 2;
			this.menuItem7.Text = "Save Assembly As";
			this.menuItem7.Click += new System.EventHandler(this.onSaveAssemblyAs);
			// 
			// menuItem3
			// 
			this.menuItem3.Index = 3;
			this.menuItem3.Text = "Exit";
			this.menuItem3.Click += new System.EventHandler(this.onExit);
			// 
			// menuItem2
			// 
			this.menuItem2.Index = 1;
			this.menuItem2.Text = "Compile";
			this.menuItem2.Click += new System.EventHandler(this.onCompile);
			// 
			// menuItem5
			// 
			this.menuItem5.Enabled = false;
			this.menuItem5.Index = 2;
			this.menuItem5.Text = "Execute";
			this.menuItem5.Click += new System.EventHandler(this.onExecute);
			// 
			// textBox1
			// 
			this.textBox1.AcceptsReturn = true;
			this.textBox1.AcceptsTab = true;
			this.textBox1.AllowDrop = true;
			this.textBox1.AutoSize = false;
			this.textBox1.Location = new System.Drawing.Point(152, 8);
			this.textBox1.Multiline = true;
			this.textBox1.Name = "textBox1";
			this.textBox1.Size = new System.Drawing.Size(744, 416);
			this.textBox1.TabIndex = 0;
			this.textBox1.Text = "";
			this.textBox1.WordWrap = false;
			// 
			// listBox1
			// 
			this.listBox1.ItemHeight = 16;
			this.listBox1.Location = new System.Drawing.Point(8, 34);
			this.listBox1.Name = "listBox1";
			this.listBox1.Size = new System.Drawing.Size(136, 388);
			this.listBox1.TabIndex = 1;
			this.listBox1.SelectedIndexChanged += new System.EventHandler(this.onSelect);
			// 
			// label1
			// 
			this.label1.Font = new System.Drawing.Font("Microsoft Sans Serif", 7.8F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((System.Byte)(0)));
			this.label1.Location = new System.Drawing.Point(8, 8);
			this.label1.Name = "label1";
			this.label1.Size = new System.Drawing.Size(100, 16);
			this.label1.TabIndex = 2;
			this.label1.Text = "Assemblies";
			// 
			// richTextBox1
			// 
			this.richTextBox1.Location = new System.Drawing.Point(912, 576);
			this.richTextBox1.Name = "richTextBox1";
			this.richTextBox1.Size = new System.Drawing.Size(88, 40);
			this.richTextBox1.TabIndex = 3;
			this.richTextBox1.Text = "richTextBox1";
			// 
			// listBox2
			// 
			this.listBox2.HorizontalScrollbar = true;
			this.listBox2.ItemHeight = 16;
			this.listBox2.Location = new System.Drawing.Point(8, 432);
			this.listBox2.Name = "listBox2";
			this.listBox2.Size = new System.Drawing.Size(888, 148);
			this.listBox2.TabIndex = 4;
			// 
			// Form1
			// 
			this.AutoScaleBaseSize = new System.Drawing.Size(6, 15);
			this.ClientSize = new System.Drawing.Size(904, 590);
			this.Controls.Add(this.listBox2);
			this.Controls.Add(this.richTextBox1);
			this.Controls.Add(this.label1);
			this.Controls.Add(this.listBox1);
			this.Controls.Add(this.textBox1);
			this.Menu = this.mainMenu1;
			this.Name = "Form1";
			this.Text = "lcsc Demo";
			this.ResumeLayout(false);

		}
		#endregion

		private AssemblyBuilder assembly = null;

		private void onCompile(object sender, System.EventArgs e) {
			assembly = demo.Compile(textBox1.Text);
			if (assembly != null) {
				menuItem5.Enabled = true;
				//menuItem7.Enabled = true;
				listBox1.Items.Add(assembly);
				listBox1.SelectedIndex = listBox1.Items.Count - 1;
			}
		}

		private void onLoad(object sender, System.EventArgs e) {
			if (openFileDialog1.ShowDialog() == DialogResult.OK) {
				StreamReader r = new StreamReader(openFileDialog1.OpenFile());
				textBox1.Text = r.ReadToEnd();
				r.Close();
			}			
		}

		private void onExit(object sender, System.EventArgs e) {
			Application.Exit();
		}

		private void onExecute(object sender, System.EventArgs e) {
			if (assembly != null)
				demo.Run(assembly);
		}

		private void onSaveAs(object sender, System.EventArgs e) {
			if (saveFileDialog1.ShowDialog() == DialogResult.OK) {
				StreamWriter w = new StreamWriter(saveFileDialog1.OpenFile());
				w.Write(textBox1.Text);
				w.Close();
			}
		}

		private void onSaveAssemblyAs(object sender, System.EventArgs e) {
			if (assembly != null && saveFileDialog1.ShowDialog() == DialogResult.OK) {
				assembly.Save(Path.GetFileName(saveFileDialog1.FileName));
			}
		
		}

		private void onSelect(object sender, System.EventArgs e) {
			Debug.Assert(sender == listBox1);
			assembly = (AssemblyBuilder)listBox1.Items[listBox1.SelectedIndex];
			if (assembly != null) {
				menuItem5.Enabled = true;
				//menuItem7.Enabled = true;
			}
		}

	}
