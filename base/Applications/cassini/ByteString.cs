//------------------------------------------------------------------------------
//   Copyright (c) Microsoft Corporation. All Rights Reserved.
//------------------------------------------------------------------------------

namespace Microsoft.VisualStudio.WebHost
{
    using System;
    using System.Collections;
    using System.Text;

    internal sealed class ByteString {
        private byte[] _bytes;
        private int _offset;
        private int _length;

        public ByteString(byte[] bytes, int offset, int length) {
            _bytes = bytes;
            _offset = offset;
            _length = length;
        }

        public byte[] Bytes { 
            get { 
                return _bytes; 
            } 
        }

        public bool IsEmpty { 
            get { 
                return (_bytes == null || _length == 0); 
            }  
        }

        public int Length { 
            get {
                return _length; 
            } 
        }

        public int Offset { 
            get { 
                return _offset; 
            } 
        }

        public byte this[int index] {
            get {
                return _bytes[_offset+index];
            }
        }

        public String GetString() {
            return GetString(Encoding.UTF8);
        }

        public String GetString(Encoding enc) {
            if (IsEmpty) {
                return String.Empty;
            }
            return enc.GetString(_bytes, _offset, _length);
        }

        public byte[] GetBytes() {
            byte[] bytes = new byte[_length];
            if (_length > 0) {
                Buffer.BlockCopy(_bytes, _offset, bytes, 0, _length);
            }
            return bytes;
        }

        public int IndexOf(char ch) {
            return IndexOf(ch, 0);
        }

        public int IndexOf(char ch, int offset) {
            for (int i = offset; i < _length; i++) {
                if (this[i] == (byte)ch) {
                    return i;
                }
            }

            return -1;
        }

        public ByteString Substring(int offset) {
            return Substring(offset, _length-offset);
        }

        public ByteString Substring(int offset, int len) {
            return new ByteString(_bytes, _offset+offset, len);
        }

        public ByteString[] Split(char sep) {
            ArrayList list = new ArrayList();

            int pos = 0;
            while (pos < _length) {
                int i = IndexOf(sep, pos);
                if (i < 0) {
                    break;
                }

                list.Add(Substring(pos, i-pos));
                pos = i+1;

                while (this[pos] == (byte)sep && pos < _length) {
                    pos++;
                }
            }

            if (pos < _length) {
                list.Add(Substring(pos));
            }

            int n = list.Count;
            ByteString[] result = new ByteString[n];
            
            for (int i = 0; i < n; i++) {
                result[i] = (ByteString)list[i];
            }

            return result;
        }
    }
}
