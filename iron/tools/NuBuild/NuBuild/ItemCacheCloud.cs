//---
//- <copyright file="ItemCacheCloud.cs" company="Microsoft Corporation">
//-     Copyright (c) Microsoft Corporation.  All rights reserved.
//- </copyright>
//---

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Globalization;
    using System.IO;
    using Microsoft.WindowsAzure.Storage;
    using Microsoft.WindowsAzure.Storage.Blob;

    /
    /
    /
    /
    public class ItemCacheCloud : IItemCache
    {
        /
        /
        /
        private readonly CloudStorageAccount storageAccount;

        /
        /
        /
        private readonly CloudBlobClient blobClient;

        /
        /
        /
        private readonly CloudBlobContainer[] cloudContainers;

        /
        /
        /
        public ItemCacheCloud()
        {
            //- -
            //- Create our CloudStorageAccount object.
            //- -
            string cloudStorageAccountString = File.ReadAllText(
                Path.Combine(BuildEngine.theEngine.getIronRoot(), "nubuild.cloud-credentials"));
            cloudStorageAccountString = cloudStorageAccountString.TrimEnd();
            this.storageAccount = CloudStorageAccount.Parse(cloudStorageAccountString);

            //- -
            //- Create our CloudBlobClient object.
            //- -
            this.blobClient = this.storageAccount.CreateCloudBlobClient();

            //- -
            //- Set up the blob storage containers.
            //- -
            Array containers = Enum.GetValues(typeof(ItemCacheContainer));
            this.cloudContainers = new CloudBlobContainer[containers.Length];
            foreach (ItemCacheContainer container in containers)
            {
                CloudBlobContainer cloudContainer = this.blobClient.GetContainerReference(container.ToString().ToLower(CultureInfo.InvariantCulture));
                cloudContainer.CreateIfNotExists();
                this.cloudContainers[(int)container] = cloudContainer;
            }
        }

        /
        /
        /
        public string Name
        {
            get { return "Cloud"; }
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            if (!cloudBlob.Exists())
            {
                return null;
            }

            using (MemoryStream memoryStream = new MemoryStream())
            {
                cloudBlob.DownloadToStream(memoryStream);
                return memoryStream.ToArray();
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
        public void FetchItemToFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemDestinationPath)
        {
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            try
            {
                cloudBlob.DownloadToFile(localFilesystemDestinationPath, FileMode.Create);
            }
            catch (Microsoft.WindowsAzure.Storage.StorageException)
            {
                throw new ObjectMissingFromCacheException(itemHash, "Item missing from cloud cache.");
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            cloudBlob.UploadFromByteArray(contents, 0, contents.Length);
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            cloudBlob.UploadFromFile(localFilesystemSourcePath, FileMode.Open);
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            cloudBlob.DeleteIfExists();
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

            foreach (CloudBlockBlob item in this.cloudContainers[(int)container].ListBlobs(null, true))
            {
                itemHashes.Add(item.Name);
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
        /
        /
        public long GetItemSize(
            ItemCacheContainer container,
            string itemHash)
        {
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            if (cloudBlob.Exists())
            {
                return cloudBlob.Properties.Length;
            }

            return -1;
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
        public bool ItemExists(
            ItemCacheContainer container,
            string itemHash)
        {
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            return cloudBlob.Exists();
        }
    }
}
