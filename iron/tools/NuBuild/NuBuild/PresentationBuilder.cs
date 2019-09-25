using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml;
using System.IO;
using System.Diagnostics;

namespace NuBuild
{
    class PresentationBuilder
    {
        //- Build-up interface
        StringBuilder sb;
        XmlWriter xw;

        public PresentationBuilder()
        {
            sb = new StringBuilder();
            //- notice no indentation, to avoid mungling text.
            xw = XmlWriter.Create(sb);
            xw.WriteStartDocument();
            xw.WriteStartElement(Presentation._xml_tag);
        }

        public Presentation fix()
        {
            xw.WriteEndElement();
            xw.WriteEndDocument();
            xw.Close();
            return new Presentation(sb.ToString());
        }

        public void text(string s) { xw.WriteString(s); }
        public void color(string color, string s)
        {
            xw.WriteStartElement(Presentation.COLOR);
            xw.WriteAttributeString(Presentation._xml_ColorValue_attr, color);
            text(s);
            xw.WriteEndElement();
        }
        void simpleTag(string tag, string s)
        {
            xw.WriteStartElement(tag);
            text(s);
            xw.WriteEndElement();
        }
        public void header(string s) { simpleTag(Presentation.HEADER, s); }
        public void line(string s) { simpleTag(Presentation.LINE, s); }
        public void spacer() { simpleTag(Presentation.SPACER, ""); }
        public void bullet(string s) { simpleTag(Presentation.BULLET, s); }
        public void pre(string s) { simpleTag(Presentation.PRE, s); }
        public void startHeader() { xw.WriteStartElement(Presentation.HEADER); }
        public void endHeader() { xw.WriteEndElement(); }
        public void startLine() { xw.WriteStartElement(Presentation.LINE); }
        public void endLine() { xw.WriteEndElement(); }
        public void startBullet() { xw.WriteStartElement(Presentation.BULLET); }
        public void endBullet() { xw.WriteEndElement(); }
    }
}
