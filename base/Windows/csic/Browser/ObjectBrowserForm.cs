using System;
using System.Drawing;
using System.Collections;
using System.ComponentModel;
using System.Windows.Forms;

namespace Browser {
	/// <summary>
	/// Summary description for ObjectBrowserForm.
	/// </summary>
	public class ObjectBrowserForm : System.Windows.Forms.Form {
		private System.Windows.Forms.Panel panel1;
		private System.Windows.Forms.Button backButton;
		private System.Windows.Forms.Button forwardButton;
		private System.Windows.Forms.MainMenu mainMenu1;
		private System.Windows.Forms.MenuItem menuItem1;
		private System.Windows.Forms.MenuItem menuItem2;
		private System.Windows.Forms.MenuItem fontMenuItem;
		private System.Windows.Forms.FontDialog fontDialog;
		/// <summary>
		/// Required designer variable.
		/// </summary>
		private System.ComponentModel.Container components = null;

		private HistoryView HV;
		private System.Windows.Forms.TreeView treeView1;
		private System.Windows.Forms.Button newButton;
		private System.Windows.Forms.MenuItem menuItem3;
		private Model model;

		public ObjectBrowserForm(object o) {
			//
			// Required for Windows Form Designer support
			//
			InitializeComponent();
			model = new Model(new object[] { o } );
			HV = new HistoryView(model);
			new ObjectTreeView(model, this.treeView1);
			this.Text = String.Format("{0}#{1}", o.GetType().Name, o.GetHashCode());
			model.ChangeObject(o);
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
		private void InitializeComponent() {
			this.panel1 = new System.Windows.Forms.Panel();
			this.forwardButton = new System.Windows.Forms.Button();
			this.backButton = new System.Windows.Forms.Button();
			this.mainMenu1 = new System.Windows.Forms.MainMenu();
			this.menuItem1 = new System.Windows.Forms.MenuItem();
			this.menuItem2 = new System.Windows.Forms.MenuItem();
			this.fontMenuItem = new System.Windows.Forms.MenuItem();
			this.fontDialog = new System.Windows.Forms.FontDialog();
			this.treeView1 = new System.Windows.Forms.TreeView();
			this.newButton = new System.Windows.Forms.Button();
			this.menuItem3 = new System.Windows.Forms.MenuItem();
			this.panel1.SuspendLayout();
			this.SuspendLayout();
			// 
			// panel1
			// 
			this.panel1.Controls.Add(this.newButton);
			this.panel1.Controls.Add(this.forwardButton);
			this.panel1.Controls.Add(this.backButton);
			this.panel1.Dock = System.Windows.Forms.DockStyle.Top;
			this.panel1.Location = new System.Drawing.Point(0, 0);
			this.panel1.Name = "panel1";
			this.panel1.Size = new System.Drawing.Size(768, 40);
			this.panel1.TabIndex = 2;
			// 
			// forwardButton
			// 
			this.forwardButton.Dock = System.Windows.Forms.DockStyle.Left;
			this.forwardButton.Location = new System.Drawing.Point(96, 0);
			this.forwardButton.Name = "forwardButton";
			this.forwardButton.Size = new System.Drawing.Size(96, 40);
			this.forwardButton.TabIndex = 1;
			this.forwardButton.Text = "Forward";
			this.forwardButton.Click += new System.EventHandler(this.forwardButton_Click);
			// 
			// backButton
			// 
			this.backButton.Dock = System.Windows.Forms.DockStyle.Left;
			this.backButton.Location = new System.Drawing.Point(0, 0);
			this.backButton.Name = "backButton";
			this.backButton.Size = new System.Drawing.Size(96, 40);
			this.backButton.TabIndex = 0;
			this.backButton.Text = "Back";
			this.backButton.Click += new System.EventHandler(this.backButton_Click);
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
			this.menuItem1.MenuItems.AddRange(new System.Windows.Forms.MenuItem[] {
																					  this.menuItem3});
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
			// treeView1
			// 
			this.treeView1.Dock = System.Windows.Forms.DockStyle.Fill;
			this.treeView1.ImageIndex = -1;
			this.treeView1.Location = new System.Drawing.Point(0, 40);
			this.treeView1.Name = "treeView1";
			this.treeView1.SelectedImageIndex = -1;
			this.treeView1.Size = new System.Drawing.Size(768, 534);
			this.treeView1.TabIndex = 3;
			// 
			// newButton
			// 
			this.newButton.Location = new System.Drawing.Point(192, 0);
			this.newButton.Name = "newButton";
			this.newButton.Size = new System.Drawing.Size(96, 40);
			this.newButton.TabIndex = 2;
			this.newButton.Text = "New";
			this.newButton.Click += new System.EventHandler(this.newButtonClick);
			// 
			// menuItem3
			// 
			this.menuItem3.Index = 0;
			this.menuItem3.Text = "Exit";
			this.menuItem3.Click += new System.EventHandler(this.onExit);
			// 
			// ObjectBrowserForm
			// 
			this.AutoScaleBaseSize = new System.Drawing.Size(6, 15);
			this.ClientSize = new System.Drawing.Size(768, 574);
			this.Controls.Add(this.treeView1);
			this.Controls.Add(this.panel1);
			this.Menu = this.mainMenu1;
			this.Name = "ObjectBrowserForm";
			this.Text = "Object Browser";
			this.panel1.ResumeLayout(false);
			this.ResumeLayout(false);

		}
		#endregion

		/// <summary>
		/// The main entry point for the application.
		/// </summary>
		/// 
		//[STAThread]

		public static void Go(object o) {
			ObjectBrowserForm form = new ObjectBrowserForm(o);
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

		private void newButtonClick(object sender, System.EventArgs e) {
			if (this.model.CurrentObject != null)
				(new ObjectBrowserForm(this.model.CurrentObject)).Show();
		}

		private void onExit(object sender, System.EventArgs e) {
			Application.Exit();
		}
	}
}
