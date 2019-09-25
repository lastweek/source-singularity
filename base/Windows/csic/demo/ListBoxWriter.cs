using System;
using System.IO;
using System.Windows.Forms;
using System.Text;

/// <summary>
/// Summary description for TextBoxWriter.
/// </summary>
public class ListBoxWriter: StringWriter {
	ListBox listbox;

	public ListBoxWriter(ListBox listbox) {
		this.listbox = listbox;
	}

	override public void Write(char value) {
		if (value == '\n') {
			listbox.Items.Add(this.GetStringBuilder().ToString());
			listbox.SelectedIndex = listbox.Items.Count - 1;
			listbox.ClearSelected();
			this.GetStringBuilder().Length = 0;
		} else if (value != '\r')
			base.Write(value);
	}

	override public void Write(string value) {
		foreach (char c in value)
			Write(c);
	}

	override public void Write(char[] buffer, int index, int count) {
		for ( ; count > 0; count--)
			Write(buffer[index++]);
	}
    
}

