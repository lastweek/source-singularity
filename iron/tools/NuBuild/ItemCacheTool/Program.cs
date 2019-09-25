//--



//--

namespace ItemCacheTool
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;
    using System.Text;
    using System.Threading.Tasks;
    using Microsoft.WindowsAzure.Storage;
    using Microsoft.WindowsAzure.Storage.Blob;
    using NuBuild;

    /
    /
    /
    public static class Program
    {
        /
        /
        /
        /
        private static void Main(string[] args)
        {
            CacheState caches = new CacheState();
            string query;
            IItemCache[] queriedCaches;
            ItemCacheContainer[] queriedContainers;
            string queriedItems;

            
            
            
            
            query = "status";
            queriedCaches = caches.GetAllCaches;
            queriedContainers = caches.GetAllContainers;
            queriedItems = string.Empty;

            
            
            
            if (args.Length != 0)
            {
                if (args.Length != 3)
                {
                    if (args.Length == 4)
                    {
                        queriedItems = args[3];
                    }
                    else
                    {
                        Usage(caches);
                        return;
                    }
                }

                query = args[0];
                queriedCaches = caches.ParseCacheName(args[1]);
                queriedContainers = caches.ParseContainerName(args[2]);

                if ((queriedCaches == null) || (queriedContainers == null))
                {
                    Usage(caches);
                    return;
                }
            }

            
            
            
            switch (query)
            {
                case "list":
                case "List":
                    {
                        CacheStatus(queriedCaches, queriedContainers, true);
                        break;
                    }

                case "compare":
                case "Compare":
                    {
                        if (queriedCaches.Length < 2)
                        {
                            Console.WriteLine("Error: can't compare fewer than two caches!");
                            Usage(caches);
                            return;
                        }

                        CompareCacheContainers(queriedCaches, queriedContainers);
                        break;
                    }

                case "status":
                case "Status":
                    {
                        CacheStatus(queriedCaches, queriedContainers, false);
                        break;
                    }

                case "delete":
                case "Delete":
                    {
                        if (args.Length < 4)
                        {
                            Console.WriteLine("Error: missing argument -- item(s) to delete.");
                            Usage(caches);
                            return;
                        }

                        DeleteItems(queriedCaches, queriedContainers, queriedItems);
                        break;
                    }
            }
        }

        /
        /
        /
        /
        private static void Usage(CacheState caches)
        {
            string containers = string.Empty;
            foreach (ItemCacheContainer container in caches.GetAllContainers)
            {
                containers += container.ToString() + " | ";
            }

            containers += " *";

            Console.WriteLine("Usage: ItemCacheTool <command> <cache> <container> [item hash]");
            Console.WriteLine("\t <command> = Compare | Delete | List | Status");
            Console.WriteLine("\t <cache> = Cloud | Local | *");
            Console.WriteLine("\t <container> = {0}", containers);
            Console.WriteLine("\t [item hash] = item to delete");
        }

        /
        /
        /
        /
        /
        /
        /
        private static void CacheStatus(
            IItemCache[] queriedCaches,
            ItemCacheContainer[] queriedContainers,
            bool listContents)
        {
            string lineTerminator = ".";
            if (listContents)
            {
                lineTerminator = ":";
            }

            foreach (IItemCache cache in queriedCaches)
            {
                foreach (ItemCacheContainer container in queriedContainers)
                {
                    HashSet<string> items = cache.GetItemsInContainer(container);
                    Console.WriteLine("{0} cache {1} container holds {2} items{3}", cache.Name, container.ToString(), items.Count, lineTerminator);
                    if (listContents)
                    {
                        foreach (string item in items)
                        {
                            Console.WriteLine(item);
                        }

                        Console.WriteLine();
                    }
                }

                Console.WriteLine();
            }
        }

        /
        /
        /
        /
        /
        private static void CompareCacheContainers(
            IItemCache[] queriedCaches,
            ItemCacheContainer[] queriedContainers)
        {
            foreach (ItemCacheContainer container in queriedContainers)
            {
                IItemCache cacheA = queriedCaches[0];
                IItemCache cacheB = queriedCaches[1];

                HashSet<string> cacheAItems = cacheA.GetItemsInContainer(container);
                HashSet<string> cacheBItems = cacheB.GetItemsInContainer(container);

                Console.WriteLine("There are {0} items in the {1} cache {2} container.", cacheAItems.Count, cacheA.Name, container.ToString());
                Console.WriteLine("There are {0} items in the {1} cache {2} container.", cacheBItems.Count, cacheB.Name, container.ToString());

                HashSet<string> syncedItems = new HashSet<string>(cacheAItems);
                syncedItems.IntersectWith(cacheBItems);
                Console.WriteLine("There are {0} items present in both cache's {1} container.", syncedItems.Count, container);
                Console.WriteLine();
            }
        }

        /
        /
        /
        /
        /
        /
        private static void DeleteItems(
            IItemCache[] queriedCaches,
            ItemCacheContainer[] queriedContainers,
            string queriedItems)
        {
            if (queriedItems == "*")
            {
                string input;
                string annoyingConfirmationString = "Yes I mean to do this!";

                Console.WriteLine("You are about to delete a large number of cache items!");
                Console.WriteLine("To proceed, please enter '{0}':", annoyingConfirmationString);
                input = Console.ReadLine();
                if (input != annoyingConfirmationString)
                {
                    Console.WriteLine("Your input didn't match.  Exiting without deleting anything.");
                    return;
                }
            }

            foreach (IItemCache cache in queriedCaches)
            {
                foreach (ItemCacheContainer container in queriedContainers)
                {
                    if (queriedItems == "*")
                    {
                        HashSet<string> items = cache.GetItemsInContainer(container);
                        foreach (string item in items)
                        {
                            cache.DeleteItem(container, item);
                        }
                    }
                    else
                    {
                        cache.DeleteItem(container, queriedItems);
                    }
                }
            }
        }
    }
}
