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
    interface Presentater
    {
        void startHeader();
        void endHeader();
        void startLine();
        void endLine();
        void startSpacer();
        void endSpacer();
        void startColor(string colorName);
        void endColor();
        void startBullet();
        void endBullet();
        void startPre();
        void endPre();
        void doText(string text);
    }

    public class HTMLPresentater : Presentater
    {
        StringBuilder document;

        public HTMLPresentater()
        {
            document = new StringBuilder();
            document.Append("<html>\n<body>\n");
        }

        public override string ToString()
        {
            document.Append("</body>\n</html>\n");
            return document.ToString();
        }

        public void startHeader() { document.Append("<h3><u>"); }
        public void endHeader() { document.Append("</u></h3>"); }

        public void startLine() { document.Append("<br>"); }
        public void endLine() { document.Append("</br>\n"); }

        public void startSpacer() { document.Append("<p>\n"); }
        public void endSpacer() { document.Append("</p>\n"); }

        public void startColor(string colorName)
        {
            string htmlColor;
            switch (colorName)
            {
                case Presentation.RED: htmlColor = "red"; break;
                case Presentation.GREEN: htmlColor = "green"; break;
                default: htmlColor = "black"; break;
            }
            document.Append("<font color=\"" + htmlColor + "\">");
        }
        public void endColor() { document.Append("</font>"); }

        public void startBullet() { document.Append("<li>"); }
        public void endBullet() { document.Append("</li>\n"); }

        public void startPre() { document.Append("<pre>"); }
        public void endPre() { document.Append("</pre>\n"); }

        public void doText(string text) { document.Append(text); }

    }

    public class ASCIIPresentater : Presentater
    {
        class ColorEnum {
            public string start;
            public string stop;
            public ColorEnum(string start, string stop) {
                this.start = start;
                this.stop = stop;
            }
            public static ColorEnum join(ColorEnum a, ColorEnum b)
            {
                return new ColorEnum(a.start+b.start, b.stop+a.stop);
            }
        }
        static ColorEnum Red = new ColorEnum("\x1b[01;41m", "\x1b[0;49m");
        static ColorEnum Green = new ColorEnum("\x1b[01;32m", "\x1b[0;0m");
        static ColorEnum BlackBackground = new ColorEnum("\x1b[01;40m", "\x1b[0;49m");
        static ColorEnum YellowBackground = new ColorEnum("\x1b[01;43m", "\x1b[0;49m");
        static ColorEnum BoldWhite = new ColorEnum("\x1b[01;37m", "\x1b[0;39m");
        static ColorEnum WhiteOnBlack = ColorEnum.join(BlackBackground, BoldWhite);
        static ColorEnum Ordinary = new ColorEnum("", "");

        StringBuilder document;
        ColorEnum colorEnum;   

        public ASCIIPresentater()
        {
            document = new StringBuilder();
        }

        public override string ToString()
        {
            return document.ToString();
        }

        public void startHeader() { document.Append(WhiteOnBlack.start); }
        public void endHeader() { document.Append(WhiteOnBlack.stop + "\n"); }

        public void startLine() { }
        public void endLine() { document.Append("\n"); }

        public void startSpacer() { }
        public void endSpacer() { document.Append("\n"); }

        public void startColor(string colorName)
        {
            Util.Assert(colorEnum == null);
            switch (colorName)
            {
                case Presentation.RED: colorEnum = Red; break;
                case Presentation.GREEN: colorEnum = Green; break;
                default: colorEnum = Ordinary; break;
            }
            document.Append(colorEnum.start);
        }
        public void endColor() { document.Append(colorEnum.stop); colorEnum = null; }

        public void startBullet() { document.Append(" * "); }
        public void endBullet() { document.Append("\n"); }

        public void startPre() { }
        public void endPre()
        {
            if (!document.ToString().EndsWith("\n"))
            {
                document.Append("\n");
            }
        }

        public void doText(string text) { document.Append(text); }

    }

}
