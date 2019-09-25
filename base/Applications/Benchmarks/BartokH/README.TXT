Hosted Bartok requires the following change to System\RuntimeType.cs:

        public override int GetHashCode() {
            return unchecked((int)(
                                 (int)Magic.addressOf(this.classVtable)
                                 + ((int)this.classVtable.arrayOf << 8 + rank)
                                 + (int)this.classVtable.structuralView));
        }
