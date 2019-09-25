// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

#include <stdio.h>
#include <string.h>

int main(int argc, char **argv)
{
    struct WAVE
    {
        char    riffId[4];
        int     riffBytes;
        char    waveId[4];
    };

    union CHUNK
    {
        struct
        {
            char    fmtId[4];
            int     fmtBytes;
            short   audioFormat;
            short   numChannels;
            int     samplesPerSec;
            int     bytesPerSec;
            short   blockAlign;
            short   bitsPerSample;
            short   byteExtra;
        } FMT;

        struct
        {
            char    dataId[4];
            int     dataBytes;
        } DATA;
    };

    for (int arg = 1; arg < argc; arg++) {
        FILE *fp = fopen(argv[arg], "rb");
        if (fp == NULL) {
            printf("Couldn't read %s\n", argv[arg]);
        }

        printf("%s\n", argv[arg]);

        WAVE wave;
        CHUNK chunk;

        fread(&wave, 1, sizeof(wave), fp);
        if (strncmp(wave.riffId, "RIFF", 4) != 0 ||
            strncmp(wave.waveId, "WAVE", 4) != 0) {
            printf("  riffId:         %-4.4s\n", wave.riffId);
            printf("  riffBytes:      %d\n", wave.riffBytes);
            printf("  waveId:         %-4.4s\n", wave.waveId);
            printf("!!!\n");
            return 1;
        }

        int offset = ftell(fp);

        while (fread(&chunk.DATA, 1, sizeof(chunk.DATA), fp) != 0) {
            if (strncmp(chunk.DATA.dataId, "data", 4) == 0) {
            }
            else if (strncmp(chunk.DATA.dataId, "fmt ", 4) == 0) {
                fseek(fp, offset, SEEK_SET);
                fread(&chunk.FMT, 1, sizeof(chunk.FMT), fp);

                if (chunk.FMT.audioFormat != 1) {
                    printf("      audioFormat:    %d\n", chunk.FMT.audioFormat);
                    printf("!!!\n");
                    break;
                }
                if (chunk.FMT.blockAlign !=
                    (chunk.FMT.bitsPerSample * chunk.FMT.numChannels) / 8) {
                    printf("      numChannels:    %d\n", chunk.FMT.numChannels);
                    printf("      blockAlign:     %d\n", chunk.FMT.blockAlign);
                    printf("      bitsPerSample:  %d\n", chunk.FMT.bitsPerSample);
                    printf("!!!\n");
                    break;
                }
                printf("channels=%1d samplesPerSec=%5d bitsPerSamples=%2d\n",
                       chunk.FMT.numChannels,
                       chunk.FMT.samplesPerSec,
                       chunk.FMT.bitsPerSample);
            }
            else {
                printf("    Id:             %-4.4s\n", chunk.DATA.dataId);
                printf("    Bytes:          %d\n", chunk.DATA.dataBytes);
            }

            offset += 8 + chunk.DATA.dataBytes;
            fseek(fp, offset, SEEK_SET);
        }
        fclose(fp);
    }

    return 0;

}

