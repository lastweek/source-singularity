//---
//- <copyright file="ItemCacheLocal.cs" company="Microsoft Corporation">
//-     Copyright (c) Microsoft Corporation.  All rights reserved.
//- </copyright>
//---

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Threading;

    /
    /
    /
    /
    public class ItemCacheLocal : IItemCache
    {
        /
        /
        /
        /
        private readonly string[] localPaths;

        /
        /
        /
        private object cacheLock;

        /
        /
        /
        /
        /
        /
        /
        /
        /
        public ItemCacheLocal(string localCacheDirectory)
        {
            //- -
            //- Set up the local "container" directories and paths to them.
            //- -
            Array containers = Enum.GetValues(typeof(ItemCacheContainer));
            this.localPaths = new string[containers.Length];
            foreach (ItemCacheContainer container in containers)
            {
                string directory = Path.Combine(
                    localCacheDirectory,
                    container.ToString());

                this.localPaths[(int)container] = directory;
                Directory.CreateDirectory(directory);
            }

            this.cacheLock = new object();
        }

        /
        /
        /
        public string Name
        {
            get { return "Local"; }
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
            string itemPath = this.ItemPath(container, itemHash);

            lock (this.cacheLock)
            {
                if (!File.Exists(itemPath))
                {
                    return null;
                }

                return File.ReadAllBytes(itemPath);
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
        public void FetchItemToFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemDestinationPath)
        {
            lock (this.cacheLock)
            {
                try
                {
                    File.Copy(this.ItemPath(container, itemHash), localFilesystemDestinationPath);
                }
                catch (FileNotFoundException)
                {
                    throw new ObjectMissingFromCacheException(itemHash, "Item missing from local cache.");
                }
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
        public void StoreItem(
            ItemCacheContainer container,
            string itemHash,
            byte[] contents)
        {
            string itemPath = this.ItemPath(container, itemHash);
            lock (this.cacheLock)
            {
                File.Delete(itemPath);
                File.WriteAllBytes(itemPath, contents);
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
        public void StoreItemFromFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemSourcePath)
        {
            string itemPath = this.ItemPath(container, itemHash);
            lock (this.cacheLock)
            {
                File.Delete(itemPath);
                File.Copy(localFilesystemSourcePath, itemPath);
            }
        }

        /
        /
        /
        /
        /
        /
        public HashSet<string> GetItemsInContainer(ItemCacheContainer container)
        {
            HashSet<string> itemHashes = new HashSet<string>();

            foreach (string filename in Directory.EnumerateFiles(this.localPaths[(int)container]))
            {
                itemHashes.Add(Path.GetFileName(filename));
            }

            return itemHashes;
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
            lock (this.cacheLock)
            {
                File.Delete(this.ItemPath(container, itemHash));
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
        public long GetItemSize(
            ItemCacheContainer container,
            string itemHash)
        {
            lock (this.cacheLock)
            {
                FileInfo fileInfo = new FileInfo(this.ItemPath(container, itemHash));
                if (fileInfo.Exists)
                {
                    return fileInfo.Length;
                }

                return -1;
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
        private string ItemPath(ItemCacheContainer container, string itemHash)
        {
            return Path.Combine(
                this.localPaths[(int)container],
                itemHash);
        }
    }
}
