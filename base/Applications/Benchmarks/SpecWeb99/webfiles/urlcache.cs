// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;
using System.Text;

namespace Singularity.Application.SPECWeb99.WebFiles
{
    class Cache
    {
        private const bool verbose = false;
        private UrlSet cache;
        private UrlSet free;
        private int size;

        public Cache(int cacheSize, int deckSize)
        {
            cache = new UrlSet(cacheSize);
            free = new UrlSet(deckSize);
            this.size = cacheSize;
        }

        public FileSpec GetUrl(Client/*!*/ client, int id) {
            // first check the local cache
            // then see if anyone else is generating the  global

            if (cache.pos > 0) {
                return cache.urls[--cache.pos];
            }

            // return local free to global free pool

            client.globalLock.WaitOne();
            while (free.pos > 0) {
                if (client.freeDeck.pos >= client.freeDeck.urls.Length) {
                    //Console.WriteLine(" too many free slots!");
                    free.urls[--free.pos] = null;
                    //DebugStub.Break();
                    free.pos--;
                }
                else {
                    client.freeDeck.urls[client.freeDeck.pos++] =
                        free.urls[--free.pos];
                }
            }

            // now see if there are any urls available
            // if not either wait on or generate the global deck

            while (client.urlDeck.pos == 0) {
                if (client.generatingUrls == false) {
                    //Console.WriteLine("Generating cache");
                    UrlSet temp = client.urlDeck;
                    client.urlDeck = client.spareDeck;
                    client.spareDeck = temp;
                    client.generatingUrls = true;
                    client.syncLock.WaitOne();
                    client.globalLock.ReleaseMutex();
                    client.GenerateFileSpecs();
                    client.globalLock.WaitOne();
                    client.generatingUrls = false;
                    client.syncLock.ReleaseMutex();
                }
                else {
                    //Console.WriteLine("Waiting for cache");
                    client.globalLock.ReleaseMutex();
                    client.syncLock.WaitOne();
                    client.syncLock.ReleaseMutex();
                    client.globalLock.WaitOne();
                }
            }

            // the global deck is ok -- prime our cache

            if (client.urlDeck.pos > 0) {
                for (int i = 0; i < cache.urls.Length && (client.urlDeck.pos > 0); i++) {
                    cache.urls[cache.pos++] =
                        client.urlDeck.urls[--client.urlDeck.pos];
                }
            }
            client.globalLock.ReleaseMutex();
            return cache.urls[--cache.pos];
        }

        public void FreeUrl(FileSpec url) {
            if (free.pos + 1 >= free.urls.Length) {
                //Console.WriteLine("free cache full! de-allocating");
                url = null;
                return;
            }
            free.urls[free.pos++] = url;
        }
    }
}
