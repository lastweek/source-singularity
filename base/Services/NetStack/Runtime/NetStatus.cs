///
// Microsoft Research, Cambridge
// 

namespace NetStack
{
    namespace Runtime 
    {               
        public struct NetStatus 
        {
            // the error code
            public Code errorCode;           

            // ctor
            public NetStatus(Code c)
            {
                errorCode=c;
            }

            // create an implicit cast operator
            public static implicit operator NetStatus(Code c) 
            {
                return new NetStatus(c);
            }

            // create an implicit cast operator
            public static implicit operator Code(NetStatus s) 
            {
                return s.errorCode;
            }

            // networking stack error codes
            public enum Code : byte
            {
                // nice codes...
                RT_OK                =  0x00,   // runtime is happy
                RT_DROP_NO_HANDLER   =  0x01,   // packet dropped, type handler doesn't exist
                PROTOCOL_OK          =  0x02,   // protocol is finished, packet can be recycled
                PROTOCOL_PROCESSING  =  0x03,   // more work to be done (prob by other protocols)
                PROTOCOL_DROP_CHKSUM =  0x04,   // protocol drops a packet - checksum
                RT_DROP_WRONG_DEST   =  0x05,   // destination is wrong + we are not gateway
                RT_DROP_NO_ROUTE     =  0x06,   // no route to the destination, drop it
                RT_DROP_TTL_EXPIRED  =  0x07,   // ttl has been expired, drop the packet
                PROTOCOL_DROP_NO_BUF =  0x08,   // no buffer available to accept the packet                
                PROTOCOL_DROP_ERROR  =  0x09,   // general drop error
                RT_RETRY_PENDING_ARP =  0x10,   // retry sending due to pending ARP resolution

                // error codes...
                RT_ERROR             =  0x80,  // runtime general error                
                PROTOCOL_PANIC       =  0xFF   // panic - shutdown!
            }

            public static string[] 
                ErrorMap = new string[] {
                                            "RuntimeError",
                                            "UndefinderProtocol"
                                        };

            public static bool SUCCEEDED(NetStatus.Code code)
            {
                return ((((byte)code)&0x80)==0);
            }

            public static bool FAILED(NetStatus.Code code)
            {
                return (!SUCCEEDED(code));
            }

            public static string ErrorToString(NetStatus.Code errorCode)
            {                
                return ErrorMap[((byte)errorCode)&0x7F];
            }          
        }
    }
}
