//---
//- <copyright file="ItemCacheMultiplexer.cs" company="Microsoft Corporation">
//-     Copyright (c) Microsoft Corporation.  All rights reserved.
//- </copyright>
//---

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    /
    /
    /
    /
    public class ItemCacheMultiplexer : IItemCache
    {
        /
        /
        /
        private const long MaxUploadSizeThreshold = 50 * (1 << 20);

        /
        /
        /
        private readonly ItemCacheLocal localCache;

        /
        /
        /
        private readonly ItemCacheCloud cloudCache;

        /
        /
        /
        /
        /
        /
        /
        /
        /
        private readonly BackgroundWorker backgroundWorker;

        /
        /
        /
        /
        /
        /
        internal ItemCacheMultiplexer(
            ItemCacheLocal localCache,
            ItemCacheCloud cloudCache,
            BackgroundWorker backgroundWorker)
        {
            this.localCache = localCache;
            this.cloudCache = cloudCache;
            this.backgroundWorker = backgroundWorker;
        }

        /
        /
        /
        public string Name
        {
            get { return "Multiplexer"; }
        }

        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        public byte[] FetchItem(
            ItemCacheContainer container,
            string itemHash)
        {
            byte[] contents;

            contents = this.localCache.FetchItem(container, itemHash);
            if (contents == null)
            {
                contents = this.cloudCache.FetchItem(container, itemHash);
                if (contents == null)
                {
                    return null;
                }

                this.localCache.StoreItem(container, itemHash, contents);
            }
            else
            {
                //- -
                //- Schedule cloud push on successful local read.
                //- REVIEW: Is this rare optimization really worth it?
                //- -
                this.QueueItemForCloudSync(container, itemHash);
            }

            return contents;
        }

        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        public void FetchItemToFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemDestinationPath)
        {
            try
            {
                this.localCache.FetchItemToFile(container, itemHash, localFilesystemDestinationPath);

                //- -
                //- Schedule cloud push on successful local read.
                //- REVIEW: Is this rare optimization really worth it?
                //- -
                this.QueueItemForCloudSync(container, itemHash);
            }
            catch (ObjectMissingFromCacheException)
            {
                //- -
                //- If it is missing locally, try to retrieve it from the cloud.
                //- Note we stash a copy in the local cache prior to copying it
                //- to the desired local file.
                //- -
                byte[] temp = this.cloudCache.FetchItem(container, itemHash);
                if (temp == null)
                {
                    throw new ObjectMissingFromCacheException(itemHash, "Item missing from multiplexed cache.");
                }

                this.localCache.StoreItem(container, itemHash, temp);
                this.localCache.FetchItemToFile(container, itemHash, localFilesystemDestinationPath);
            }
        }

        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        public void StoreItem(
            ItemCacheContainer container,
            string itemHash,
            byte[] contents)
        {
            this.localCache.StoreItem(container, itemHash, contents);
            this.QueueItemForCloudSync(container, itemHash);
        }

        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        public void StoreItemFromFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemSourcePath)
        {
            this.localCache.StoreItemFromFile(container, itemHash, localFilesystemSourcePath);
            this.QueueItemForCloudSync(container, itemHash);
        }

        /
        /
        /
        /
        /
        /
        /
        /
        /
        public void DeleteItem(
            ItemCacheContainer container,
            string itemHash)
        {
            //- -
            //- REVIEW: What to do here?  Delete from both caches? Nothing?
            //- -
        }

        /
        /
        /
        /
        /
        /
        public HashSet<string> GetItemsInContainer(ItemCacheContainer container)
        {
            //- -
            //- REVIEW: What to return here?  Both caches contents? Nothing?
            //- -
            return new HashSet<string>();
        }

        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        public long GetItemSize(
            ItemCacheContainer container,
            string itemHash)
        {
            //- -
            //- REVIEW: What to return here?  Check both caches?
            //- -
            return this.localCache.GetItemSize(container, itemHash);
        }

        /
        /
        /
        /
        /
        /
        /
        private void QueueItemForCloudSync(
            ItemCacheContainer container,
            string itemHash)
        {
            this.backgroundWorker.QueueWork(this.CheckForAndOrUploadMissingItem, container, itemHash);
        }

        /
        /
        /
        /
        /
        /
        /
        /
        private void CheckForAndOrUploadMissingItem(
            object containerObject,
            object itemHashObject)
        {
            ItemCacheContainer container = (ItemCacheContainer)containerObject;
            string itemHash = (string)itemHashObject;

            if (this.localCache.GetItemSize(container, itemHash) > MaxUploadSizeThreshold)
            {
                Logger.WriteLine(string.Format(
                    "Warning: skipping upload of {0} because it's really big. Compress?",
                    itemHash));
                return;
            }

            //- -
            //- Check if the item is already present in the cloud cache.
            //- TODO present doesn't mean we don't want to overwrite it (eg when
            //- replacing a Failed verification result with a succeeding one.)
            //- -
            if (this.cloudCache.ItemExists(container, itemHash))
            {
                return;
            }

            //- -
            //- The item is missing from the cloud cache.  Upload it.
            //- -
            byte[] temp = this.localCache.FetchItem(container, itemHash);
            if (temp == null)
            {
                //- This should never happen barring a serious logic error.
                throw new ObjectMissingFromCacheException(itemHash, "Can't upload non-existant cache item!");
            }

            this.cloudCache.StoreItem(container, itemHash, temp);
        }

#if false
        /
        /
        /
        /
        /
        //- REVIEW: a lot of boilerplate code just to hook one call.  Better way to do this?
        /
        private class MultiplexerWrappedStream : Stream
        {
            /
            /
            /
            private bool disposed;

            /
            /
            /
            private Stream stream;

            /
            /
            /
            private ItemCacheMultiplexer multiplexer;

            /
            /
            /
            private ItemCacheContainer container;

            /
            /
            /
            private string itemHash;

            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            public MultiplexerWrappedStream(
                Stream stream,
                ItemCacheMultiplexer multiplexer,
                ItemCacheContainer container,
                string itemHash)
            {
                this.stream = stream;
                this.multiplexer = multiplexer;
                this.container = container;
                this.itemHash = itemHash;
            }

            /
            /
            /
            /
            public override bool CanRead
            {
                get { return this.stream.CanRead; }
            }

            /
            /
            /
            /
            public override bool CanSeek
            {
                get { return this.stream.CanSeek; }
            }

            /
            /
            /
            /
            public override bool CanWrite
            {
                get { return this.stream.CanWrite; }
            }

            /
            /
            /
            public override long Length
            {
                get { return this.stream.Length; }
            }

            /
            /
            /
            public override long Position
            {
                get
                {
                    return this.stream.Position;
                }

                set
                {
                    this.stream.Position = value;
                }
            }

            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            public override int Read(byte[] buffer, int offset, int count)
            {
                return this.stream.Read(buffer, offset, count);
            }

            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            public override void Write(byte[] buffer, int offset, int count)
            {
                this.stream.Write(buffer, offset, count);
            }

            /
            /
            /
            /
            public override void Flush()
            {
                this.stream.Flush();
            }

            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            /
            public override long Seek(long offset, SeekOrigin origin)
            {
                return this.stream.Seek(offset, origin);
            }

            /
            /
            /
            /
            /
            /
            public override void SetLength(long value)
            {
                this.stream.SetLength(value);
            }

            /
            /
            /
            /
            /
            /
            protected override void Dispose(bool disposing)
            {
                if (this.disposed)
                {
                    return;
                }

                if (disposing)
                {
                    this.stream.Dispose();
                    this.multiplexer.QueueItemForCloudSync(this.container, this.itemHash);
                }

                this.disposed = true;
                base.Dispose(disposing);
            }
        }
#endif
    }
}
