////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Register.cs
//
//  Note:   PnP Device Type Registration and Base Initialization.
//

using System;
using System.Collections;

using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;

namespace Microsoft.Singularity.Drivers
{
    public sealed class Devices
    {
        public static void RegisterPnpResources()
        {
            RegisterOmap3430Devices();
        }

        // Now that we use metadata, this only registers drivers that do not run
        // in separate processes.  All external processes are registered through
        // the IoSystem.Initialize() code.
        public static void RegisterInternalDrivers()
        {
        }

        private static void RegisterOmap3430Devices()
        {
            // Fake that PNP works on the OMAP
            AdHocDevices dev = new AdHocDevices(100);

            dev.Add("/arm/ti/3430/INTCPS",
                    new IoRange[] {
                        new IoMemoryRange(0x48200000, 0x1000, Access.ReadWrite)});

            dev.Add("/arm/ti/3430/NMPU",        // MPU emulation (EMUINT)
                    new IoRange[] {
                        new IoIrqRange(0, 1),   // MPU emulation (EMUINT)
                        new IoIrqRange(1, 1),   // MPU emulation (COMMRX)
                        new IoIrqRange(2, 1),   // MPU emulation (COMMTX)
                        new IoIrqRange(3, 1),   // MPU emulation (NMPUIRQ)
                        });
            dev.Add("/arm/ti/3430/D3D",         // 3G coprocessor (stacked modem)
                    new IoRange[] {
                        new IoIrqRange(8, 1),   // modem reset due to security violation (D2DSEC)
                        new IoIrqRange(88, 1)   // 3G coprocessor (stacked modem) (D2DFRONT)
                        });
            dev.Add("/arm/ti/3430/GFX",         // Display Subsystem module
                    new IoRange[] {
                        new IoMemoryRange(((!)Platform.ThePlatform).IsaCsns,
                                          0x00025800, Access.ReadWrite),
                        new IoMemoryRange(0x48050400, 0x400, Access.ReadWrite),
                        new IoIrqRange(21, 1),  // GFX 2D/3D graphics module
                        new IoIrqRange(25, 1)   // Display Subsystem module
                        });
            dev.Add("/arm/ti/3430/FAC",         // FAC module (FAC) Pretend Keyboard
                    new IoRange[] {
                        new IoIrqRange(85, 1)});
            dev.Add("/arm/ti/3430/FPKA",
                    new IoRange[] {
                        new IoIrqRange(50, 1),  // FPKA_READY_N - PKA crypto-accelerator
                        new IoIrqRange(64, 1)   // FPKA_RERROR_N - PKA crypto-accelerator
                        });
            dev.Add("/arm/ti/3430/FSUSB",       // Full-Speed USB device controller (FSUSB)
                    new IoRange[] {
                        new IoIrqRange(75, 1),  // FSUSB_GENI - Full-Speed USB device ctrlr GENI
                        new IoIrqRange(76, 1),  // FSUSB_NONISO - Full-Speed USB device ctrl non-ISO
                        new IoIrqRange(77, 1),  // FSUSB_ISO - Full-Speed USB device ISO
                        new IoIrqRange(78, 1),  // FSUSB_IRQ - Full-Speed USB host controlled
                        new IoIrqRange(79, 1),  // FSUSB_SOF - Full-Speed USB host start-of-frame
                        new IoIrqRange(80, 1),  // FSUSB_OTG - Full-Speed USB OTG
                        });
            dev.Add("/arm/ti/3430/GPIO_MPU",    // GPIO module 1 (GPIO1_MPU)
                    new IoRange[] {
                        new IoIrqRange(29, 1)});
            dev.Add("/arm/ti/3430/GPIO_MPU",    // GPIO module 2 (GPIO2_MPU)
                    new IoRange[] {
                        new IoIrqRange(30, 1)});
            dev.Add("/arm/ti/3430/GPIO_MPU",    // GPIO module 3 (GPIO3_MPU)
                    new IoRange[] {
                        new IoIrqRange(31, 1)});
            dev.Add("/arm/ti/3430/GPIO_MPU",    // GPIO module 4 (GPIO4_MPU)
                    new IoRange[] {
                        new IoIrqRange(32, 1)});
            dev.Add("/arm/ti/3430/GPIO_MPU",    // GPIO module 5 (GPIO5_MPU)
                    new IoRange[] {
                        new IoIrqRange(33, 1)});
            dev.Add("/arm/ti/3430/GPIO_MPU",    // GPIO module 6 (GPIO6_MPU)
                    new IoRange[] {
                        new IoIrqRange(34, 1)});
            dev.Add("/arm/ti/3430/GPMC",        // general-purpose memory controller (GPMC)
                    new IoRange[] {
                        new IoIrqRange(20, 1)});
            dev.Add("/arm/ti/3430/GPTIMER1",    // general-purpose timer 1 (GPT1)
                    new IoRange[] {
                        new IoMemoryRange(0x48318000, 0x1000, Access.ReadWrite),
                        new IoIrqRange(37, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 2 (GPT2)
                    new IoRange[] {
                        new IoIrqRange(38, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 3 (GPT3)
                    new IoRange[] {
                        new IoIrqRange(39, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 4 (GPT4)
                    new IoRange[] {
                        new IoIrqRange(40, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 5 (GPT5)
                    new IoRange[] {
                        new IoIrqRange(41, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 6 (GPT6)
                    new IoRange[] {
                        new IoIrqRange(42, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 7 (GPT7)
                    new IoRange[] {
                        new IoIrqRange(43, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 8 (GPT8)
                    new IoRange[] {
                        new IoIrqRange(44, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 9 (GPT9)
                    new IoRange[] {
                        new IoIrqRange(45, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 10 (GPT10)
                    new IoRange[] {
                        new IoIrqRange(46, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 11 (GPT11)
                    new IoRange[] {
                        new IoIrqRange(47, 1)});
            dev.Add("/arm/ti/3430/GPT",         // general-purpose timer 12 (GPT12)
                    new IoRange[] {
                        new IoIrqRange(95, 1)});
            dev.Add("/arm/ti/3430/HDQ",         // HDQ/One-wire (HDQ)
                    new IoRange[] {
                        new IoIrqRange(58, 1)});
            dev.Add("/arm/ti/3430/HSUSB",       // High-Speed USB OTG controller (HSUSB)
                    new IoRange[] {
                        new IoIrqRange(92, 1),  // HSUSB_MC_NINT - High-Speed USB OTG controller
                        new IoIrqRange(93, 1)   // HSUSB_DMA_NINT - High-Speed USB OTG DMA ctrl
                        });
            dev.Add("/arm/ti/3430/I2C",         // I2C module 1 (I2C1)
                    new IoRange[] {
                        new IoMemoryRange(0x48070000, 0x80, Access.ReadWrite),
                        new IoIrqRange(56, 1)});
            dev.Add("/arm/ti/3430/I2C",         // I2C module 2 (I2C2)
                    new IoRange[] {
                        new IoIrqRange(57, 1)});
            dev.Add("/arm/ti/3430/I2C",         // I2C module 3 (I2C3)
                    new IoRange[] {
                        new IoIrqRange(61, 1)});
            dev.Add("/arm/ti/3430/IVA2",        // IVA2 MMU (IVA2_MMU)
                    new IoRange[] {
                        new IoIrqRange(28, 1)});
            dev.Add("/arm/ti/3430/MCBSP",       // McBSP module 1 (MCBSP1)
                    new IoRange[] {
                        new IoIrqRange(16, 1),  // McBSP module 1 (MCBSP1)
                        new IoIrqRange(59, 1),  // McBSP module 1 transmit (MCBSP1_TX)
                        new IoIrqRange(60, 1)   // McBSP module 1 receive (MCBSP1_RX)
                        });
            dev.Add("/arm/ti/3430/MCBSP;/arm/ti/3430/MCBSP_ST", // McBSP module 2 (MCBSP2)
                    new IoRange[] {
                        new IoIrqRange(17, 1),  // McBSP module 2 (MCBSP2)
                        new IoIrqRange(62, 1),  // McBSP module 2 transmit (MCBSP2_TX)
                        new IoIrqRange(63, 1),  // McBSP module 2 receive (MCBSP2_RX)
                        new IoIrqRange(4, 1)    // Sidestone MCBSP2 overflow (MCBSP2_ST)
                        });
            dev.Add("/arm/ti/3430/MCBSP;/arm/ti/3430/MCBSP_ST", // McBSP module 3 (MCBSP3)
                    new IoRange[] {
                        new IoIrqRange(22, 1),  // McBSP module 3 (MCBSP3)
                        new IoIrqRange(89, 1),  // McBSP module 3 transmit (MCBSP3_TX)
                        new IoIrqRange(90, 1),  // McBSP module 3 receive (MCBSP3_RX)
                        new IoIrqRange(5, 1)    // Sidestone MCBSP3 overflow (MCBSP3_ST)
                        });
            dev.Add("/arm/ti/3430/MCBSP",       // McBSP module 4 (MCBSP4)
                    new IoRange[] {
                        new IoIrqRange(23, 1),  // McBSP module 4 (MCBSP4)
                        new IoIrqRange(54, 1),  // McBSP module 4 transmit (MCBSP4_TX)
                        new IoIrqRange(55, 1)   // McBSP module 4 receive (MCBSP4_RX)
                        });
            dev.Add("/arm/ti/3430/MCBSP",       // McBSP module 5 (MCBSP5)
                    new IoRange[] {
                        new IoIrqRange(27, 1),  // McBSP module 5 (MCBSP5)
                        new IoIrqRange(81, 1),  // McBSP module 5 transmit (MCBSP5_TX)
                        new IoIrqRange(82, 1)   // McBSP module 5 receive (MCBSP5_RX)
                        });
            dev.Add("/arm/ti/3430/MG",          // MG function (MG)
                    new IoRange[] {
                        new IoIrqRange(53, 1)});
            dev.Add("/arm/ti/3430/MMC",         // MMC/SD module 2 (MMC1)
                    new IoRange[] {
                        new IoIrqRange(83, 1)});
            dev.Add("/arm/ti/3430/MMC",         // MMC/SD module 2 (MMC2)
                    new IoRange[] {
                        new IoIrqRange(86, 1)});
            dev.Add("/arm/ti/3430/MPU",         // MPU ICR (MPU_ICR)
                    new IoRange[] {
                        new IoIrqRange(87, 1)});
            dev.Add("/arm/ti/3430/MS",          // MS-PRO module (MS)
                    new IoRange[] {
                        new IoIrqRange(84, 1)});
            dev.Add("/arm/ti/3430/Mailbox",     // Mailbox user 0 request (Mailbox0)
                    new IoRange[] {
                        new IoIrqRange(26, 1)});
            dev.Add("/arm/ti/3430/PRCM_MPU",    // PRCM module (PRCM_MPU)
                    new IoRange[] {
                        new IoIrqRange(11, 1)});
            dev.Add("/arm/ti/3430/RNG",         // RNG module (RNG)
                    new IoRange[] {
                        new IoIrqRange(52, 1)});
            dev.Add("/arm/ti/3430/SDMA",        // system DMA 0 (SDMA0)
                    new IoRange[] {
                        new IoIrqRange(12, 1)});
            dev.Add("/arm/ti/3430/SDMA",        // system DMA 1 (SDMA1)
                    new IoRange[] {
                        new IoIrqRange(13, 1)});
            dev.Add("/arm/ti/3430/SDMA",        // system DMA 2 (SDMA2)
                    new IoRange[] {
                        new IoIrqRange(14, 1)});
            dev.Add("/arm/ti/3430/SDMA",        // system DMA 3 (SDMA3)
                    new IoRange[] {
                        new IoIrqRange(15, 1)});
            dev.Add("/arm/ti/3430/SHA1MD5",     // SHA-1/MD5 crypto-accelerator
                    new IoRange[] {
                        new IoIrqRange(49, 1),  // SHA-1/MD5 crypto-accelerator 2 (SHA1MD52)
                        new IoIrqRange(51, 1)   // SHA-1/MD5 crypto-accelerator 1 (SHA1MD51)
                        });
            dev.Add("/arm/ti/3430/SMX",         // SMX
                    new IoRange[] {
                        new IoIrqRange(9, 1),   // SMX debug error (SMX_DBG)
                        new IoIrqRange(10, 1)   // SMX application error (SMX_APP)
                        });
            dev.Add("/arm/ti/3430/SPI",         // McSPI module 1 (SPI1)
                    new IoRange[] {
                        new IoIrqRange(65, 1)});
            dev.Add("/arm/ti/3430/SPI",         // McSPI module 2 (SPI2)
                    new IoRange[] {
                        new IoIrqRange(66, 1)});
            dev.Add("/arm/ti/3430/SPI",         // McSPI module 3 (SPI3)
                    new IoRange[] {
                        new IoIrqRange(91, 1)});
            dev.Add("/arm/ti/3430/SPI",         // McSPI module 4 (SPI4)
                    new IoRange[] {
                        new IoIrqRange(48, 1)});
            dev.Add("/arm/ti/3430/SR",          // SmartReflex 1 (SR1)
                    new IoRange[] {
                        new IoIrqRange(18, 1)});
            dev.Add("/arm/ti/3430/SR",          // SmartReflex 2 (SR2)
                    new IoRange[] {
                        new IoIrqRange(19, 1)});
            dev.Add("/arm/ti/3430/SSI",         // Dual SSI (SSI_GDD)
                    new IoRange[] {
                        new IoIrqRange(67, 1),  // Dual SSI port 1 request 0 (SSI_P1_MPU0)
                        new IoIrqRange(68, 1),  // Dual SSI port 1 request 1 (SSI_P1_MPU1)
                        new IoIrqRange(69, 1),  // Dual SSI port 2 request 0 (SSI_P2_MPU0)
                        new IoIrqRange(70, 1),  // Dual SSI port 2 request 1 (SSI_P2_MPU1)
                        new IoIrqRange(71, 1)   // Dual SSI GDD (SSI_GDD_MPU)
                        });
            dev.Add("/arm/ti/3430/SSM_ABORT",   // MPU subsystem secure state-machine abort (SSM_ABORT)
                    new IoRange[] {
                        new IoIrqRange(6, 1)});
            dev.Add("/arm/ti/3430/UART",        // UART1 (UART1)
                    new IoRange[] {
                        new IoIrqRange(72, 1)});
            dev.Add("/arm/ti/3430/UART",        // UART2 (UART2)
                    new IoRange[] {
                        new IoIrqRange(73, 1)});
            dev.Add("/arm/ti/3430/UART",        // UART3 (UART3)
                    new IoRange[] {
                        new IoIrqRange(74, 1)});
            dev.Add("/arm/ti/3430/WDT3",        // watchdog timer module 3 overflow (WDT3)
                    new IoRange[] {
                        new IoIrqRange(36, 1)});
            dev.Add("/arm/ti/3430/SYSN",        // external interrupt line (SYSN)
                    new IoRange[] {
                        new IoIrqRange(7, 1)});

            IoSystem.AddDevicesToTree(dev.List, "/fixed0/", false);
            IoSystem.Dump(true);
        }

        private class AdHocDevices
        {
            private SortedList! list;

            internal SortedList List
            {
                get {
                    return list;
                }
            }

            internal AdHocDevices(int capacity)
            {
                list = new SortedList(capacity);
            }

            internal void Add(String signature, IoRange[] ranges)
            {
                string iter = (!)(list.Count.ToString("d3"));

                list.Add(iter, new PnpConfig(new String[] { signature }, ranges));
            }
        }
    }
}
