using System;
using System.Drawing;
using System.Collections;
using System.ComponentModel;
using System.Windows.Forms;
//using System.Data;

namespace Browser {
	/// <summary>
	/// Summary description for BrowserForm.
	/// </summary>
	public class BrowserForm : System.Windows.Forms.Form {
		private System.Windows.Forms.Panel panel1;
		private System.Windows.Forms.Button backButton;
		private System.Windows.Forms.Button forwardButton;
		private System.Windows.Forms.Splitter splitter1;
		private System.Windows.Forms.MainMenu mainMenu1;
		private System.Windows.Forms.MenuItem menuItem1;
		private System.Windows.Forms.MenuItem menuItem2;
		private System.Windows.Forms.MenuItem fontMenuItem;
		private System.Windows.Forms.FontDialog fontDialog;
		private System.Windows.Forms.Button parentButton;
		/// <summary>
		/// Required designer variable.
		/// </summary>
		private System.ComponentModel.Container components = null;

		private System.Windows.Forms.TabControl sourceTabControl;
		private System.Windows.Forms.Button addButton;
		private System.Windows.Forms.Button addILButton;
		private System.Windows.Forms.Button addCodeDomTreeButton;

		private ParentView PV;
		private HistoryView HV;
		private Model model;

		public BrowserForm(IEnumerable roots) {
			//
			// Required for Windows Form Designer support
			//
			InitializeComponent();

			model = new Model(roots);
			HV = new HistoryView(model);
			PV = new ParentView(model);
			new SourceTabView(model, sourceTabControl, new NewControl(SourceTextView.NewControl));
		}

		/// <summary>
		/// Clean up any resources being used.
		/// </summary>
		protected override void Dispose( bool disposing ) {
			if( disposing ) {
				if (components != null) {
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
		private void InitializeComponent()
		{
			this.panel1 = new System.Windows.Forms.Panel();
			this.addCodeDomTreeButton = new System.Windows.Forms.Button();
			this.addILButton = new System.Windows.Forms.Button();
			this.addButton = new System.Windows.Forms.Button();
			this.parentButton = new System.Windows.Forms.Button();
			this.forwardButton = new System.Windows.Forms.Button();
			this.backButton = new System.Windows.Forms.Button();
			this.splitter1 = new System.Windows.Forms.Splitter();
			this.mainMenu1 = new System.Windows.Forms.MainMenu();
			this.menuItem1 = new System.Windows.Forms.MenuItem();
			this.menuItem2 = new System.Windows.Forms.MenuItem();
			this.fontMenuItem = new System.Windows.Forms.MenuItem();
			this.fontDialog = new System.Windows.Forms.FontDialog();
			this.sourceTabControl = new System.Windows.Forms.TabControl();
			this.panel1.SuspendLayout();
			this.SuspendLayout();
			// 
			// panel1
			// 
			this.panel1.Controls.AddRange(new System.Windows.Forms.Control[] {
																				 this.addCodeDomTreeButton,
																				 this.addILButton,
																				 this.addButton,
																				 this.parentButton,
																				 this.forwardButton,
																				 this.backButton});
			this.panel1.Dock = System.Windows.Forms.DockStyle.Top;
			this.panel1.Name = "panel1";
			this.panel1.Size = new System.Drawing.Size(1112, 56);
			this.panel1.TabIndex = 2;
			// 
			// addCodeDomTreeButton
			// 
			this.addCodeDomTreeButton.Dock = System.Windows.Forms.DockStyle.Left;
			this.addCodeDomTreeButton.Location = new System.Drawing.Point(608, 0);
			this.addCodeDomTreeButton.Name = "addCodeDomTreeButton";
			this.addCodeDomTreeButton.Size = new System.Drawing.Size(160, 56);
			this.addCodeDomTreeButton.TabIndex = 6;
			this.addCodeDomTreeButton.Text = "Add CodeDom Browser";
			this.addCodeDomTreeButton.Click += new System.EventHandler(this.addCodeDomTreeBrowser_Click);
			// 
			// addILButton
			// 
			this.addILButton.Dock = System.Windows.Forms.DockStyle.Left;
			this.addILButton.Location = new System.Drawing.Point(472, 0);
			this.addILButton.Name = "addILButton";
			this.addILButton.Size = new System.Drawing.Size(136, 56);
			this.addILButton.TabIndex = 5;
			this.addILButton.Text = "Add IL Browser";
			this.addILButton.Click += new System.EventHandler(this.addILButton_Click);
			// 
			// addButton
			// 
			this.addButton.Dock = System.Windows.Forms.DockStyle.Left;
			this.addButton.Location = new System.Drawing.Point(280, 0);
			this.addButton.Name = "addButton";
			this.addButton.Size = new System.Drawing.Size(192, 56);
			this.addButton.TabIndex = 3;
			this.addButton.Text = "Add Object Browser";
			this.addButton.Click += new System.EventHandler(this.addButton_Click);
			// 
			// parentButton
			// 
			this.parentButton.Dock = System.Windows.Forms.DockStyle.Left;
			this.parentButton.Location = new System.Drawing.Point(192, 0);
			this.parentButton.Name = "parentButton";
			this.parentButton.Size = new System.Drawing.Size(88, 56);
			this.parentButton.TabIndex = 2;
			this.parentButton.Text = "Parent";
			this.parentButton.Click += new System.EventHandler(this.parentButton_Click);
			// 
			// forwardButton
			// 
			this.forwardButton.Dock = System.Windows.Forms.DockStyle.Left;
			this.forwardButton.Location = new System.Drawing.Point(96, 0);
			this.forwardButton.Name = "forwardButton";
			this.forwardButton.Size = new System.Drawing.Size(96, 56);
			this.forwardButton.TabIndex = 1;
			this.forwardButton.Text = "Forward";
			this.forwardButton.Click += new System.EventHandler(this.forwardButton_Click);
			// 
			// backButton
			// 
			this.backButton.Dock = System.Windows.Forms.DockStyle.Left;
			this.backButton.Name = "backButton";
			this.backButton.Size = new System.Drawing.Size(96, 56);
			this.backButton.TabIndex = 0;
			this.backButton.Text = "Back";
			this.backButton.Click += new System.EventHandler(this.backButton_Click);
			// 
			// splitter1
			// 
			this.splitter1.Dock = System.Windows.Forms.DockStyle.Right;
			this.splitter1.Location = new System.Drawing.Point(1109, 56);
			this.splitter1.Name = "splitter1";
			this.splitter1.Size = new System.Drawing.Size(3, 335);
			this.splitter1.TabIndex = 4;
			this.splitter1.TabStop = false;
			// 
			// mainMenu1
			// 
			this.mainMenu1.MenuItems.AddRange(new System.Windows.Forms.MenuItem[] {
																					  this.menuItem1,
																					  this.menuItem2});
			// 
			// menuItem1
			// 
			this.menuItem1.Index = 0;
			this.menuItem1.Text = "File";
			// 
			// menuItem2
			// 
			this.menuItem2.Index = 1;
			this.menuItem2.MenuItems.AddRange(new System.Windows.Forms.MenuItem[] {
																					  this.fontMenuItem});
			this.menuItem2.Text = "Edit";
			// 
			// fontMenuItem
			// 
			this.fontMenuItem.Index = 0;
			this.fontMenuItem.Text = "Change Font";
			this.fontMenuItem.Click += new System.EventHandler(this.fontMenuItem_Click);
			// 
			// fontDialog
			// 
			this.fontDialog.FontMustExist = true;
			// 
			// sourceTabControl
			// 
			this.sourceTabControl.Alignment = System.Windows.Forms.TabAlignment.Bottom;
			this.sourceTabControl.Dock = System.Windows.Forms.DockStyle.Fill;
			this.sourceTabControl.Location = new System.Drawing.Point(0, 56);
			this.sourceTabControl.Multiline = true;
			this.sourceTabControl.Name = "sourceTabControl";
			this.sourceTabControl.SelectedIndex = 0;
			this.sourceTabControl.Size = new System.Drawing.Size(1109, 335);
			this.sourceTabControl.TabIndex = 6;
			// 
			// BrowserForm
			// 
			this.AutoScaleBaseSize = new System.Drawing.Size(6, 15);
			this.ClientSize = new System.Drawing.Size(1112, 391);
			this.Controls.AddRange(new System.Windows.Forms.Control[] {
																		  this.sourceTabControl,
																		  this.splitter1,
																		  this.panel1});
			this.Menu = this.mainMenu1;
			this.Name = "BrowserForm";
			this.Text = "Source/Object Browser";
			this.panel1.ResumeLayout(false);
			this.ResumeLayout(false);

		}
		#endregion

		/// <summary>
		/// The main entry point for the application.
		/// </summary>
		/// 
		//[STAThread]

		public static void Go(compilation o) {
			BrowserForm form = new BrowserForm(o.inputs);
			Application.Run(form);
		}

		private void backButton_Click(object sender, System.EventArgs e) {
			HV.Back();
		}

		private void forwardButton_Click(object sender, System.EventArgs e) {
			HV.Forward();
		}

		private void fontMenuItem_Click(object sender, System.EventArgs e) {
			if(fontDialog.ShowDialog() != DialogResult.Cancel ) {
				this.Font = fontDialog.Font;
			}
		}

		private void parentButton_Click(object sender, System.EventArgs e) {
			PV.Parent();
		}

		private void addBrowser(Control ctl) {
			int count = 0;
			foreach (Control c in this.Controls) {
				if (c.Dock == DockStyle.Fill || c.Dock == DockStyle.Left) {
					count += 1;
				} else {
					break;
				}
			}
			float ratio = count/(float)(count+1);
			foreach (Control c in this.Controls) {
				int width = c.Size.Width;
				if (c.Dock == DockStyle.Fill || c.Dock == DockStyle.Left) {
					c.Dock = DockStyle.Left;
					c.Size = new Size((int)(width * ratio), c.Size.Height);
				} else {
					break;
				}
			}
			Splitter spl = new Splitter();
			spl.Dock = DockStyle.Left;

			ctl.Dock = DockStyle.Fill;

			this.SuspendLayout();
			this.Controls.Add(spl);
			this.Controls.SetChildIndex(spl, 0);
			this.Controls.Add(ctl);
			this.Controls.SetChildIndex(ctl, 0);
			this.ResumeLayout();
		}

		private void addButton_Click(object sender, System.EventArgs e) {
			addBrowser(ObjectTreeView.NewBrowser(this.model));
		}

		private void addCodeDomTreeBrowser_Click(object sender, System.EventArgs e) {
			addBrowser(CodeDomTreeView.NewBrowser(this.model));
		}

		private void addILButton_Click(object sender, System.EventArgs e) {
			addBrowser(ILTextView.NewBrowser(this.model));
		}
	}
}
