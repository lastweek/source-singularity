////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

using System;
using System.Text;
using System.GC;
using System.Runtime.Remoting;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Collections;
using System.Diagnostics;

using Microsoft.Singularity;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.Io;

using Microsoft.Singularity.Channels;
using Keyboard = Microsoft.Singularity.Io.Keyboard;

namespace Microsoft.Singularity.Shell
{
    public class Pong
    {
        const int screenWidth = 1024;
        const int screenHeight = 768;

        const int paddleWidth = 16;
        const int paddleHeight = 128;

        const int ballSize = 8;

        const double paddleSpeed = 0.20;
        const double ballSpeed = 0.35;

        const double ballStartAngle = Math.PI / 8;
        const double ballMaxAngle = Math.PI / 3;

        const int screenMinX = 0;
        const int screenMinY = 0;

        const int screenMaxX = screenMinX + screenWidth - 1;
        const int screenMaxY = screenMinY + screenHeight - 1;

        const int paddleMin = screenMinY;
        const int paddleMax = screenMaxY - paddleHeight;

        const int ballMinX = screenMinX + paddleWidth;
        const int ballMaxX = screenMaxX - paddleWidth - ballSize;

        const int ballMinY = screenMinY;
        const int ballMaxY = screenMaxY - ballSize;

        const int paddleInit = screenMinY + ((screenHeight - paddleHeight) / 2);

        double ballX = 0.0;
        double ballY = 0.0;
        double ballAngle = 0.0;

        int ballDrawX = 0;
        int ballDrawY = 0;

        double[] paddlesY = new double [2] { paddleInit, paddleInit };

        int[] paddlesDrawX = new int [2] { screenMinX,
                                           screenMaxX - paddleWidth + 1 };

        int[] paddlesDrawY = new int [2] { paddleInit, paddleInit };

        bool[] inputUp   = new bool [2] { false, false };
        bool[] inputDown = new bool [2] { false, false };

        int[] scores = new int [2] { 0, 0 };

        int lastWinner = 0;

        bool done = false;
        bool playing = false;

        ISvgaDevice svga = null;

        Random random = new Random();

        public static KeyboardDeviceContract.Imp OpenKeyboard(string! devName)
        {
            KeyboardDeviceContract.Exp! exp;
            KeyboardDeviceContract.Imp! imp;
            KeyboardDeviceContract.NewChannel(out imp, out exp);

            // get NS endpoint
            DirectoryServiceContract.Imp ns = DirectoryService.NewClientEndpoint();

            bool success = false;
            ns.SendBind(Bitter.FromString2(devName),exp);
            switch receive {
                case ns.AckBind():
                    success = true;
                    break;
                case ns.NakBind(exp):
                    delete exp;
                    break;
                case ns.ChannelClosed():
                    break;
            }

            if (!success) {
                DebugStub.Print("OpenKeyboard lookup of {0} failed.\n",
                                __arglist(devName);

                delete imp;
                delete ns;
                return null;
            }

            switch receive {
                case imp.Success():
                    break;
                case unsatisfiable:
                    throw new Exception("Didn't imp.RecvAckConnect");
                    break;
            }

            delete ns;
            return imp;
        }


        public static VideoDeviceContract.Imp OpenVideo(string! devName)
        {
            VideoDeviceContract.Exp! exp;
            VideoDeviceContract.Imp! imp;
            VideoDeviceContract.NewChannel(out imp, out exp);

            // get NS endpoint
            DirectoryServiceContract.Imp ns = DirectoryService.NewClientEndpoint();

            bool success = false;
            ns.SendBind(Bitter.FromString2(devName),exp);
            switch receive {
                case ns.AckBind():
                    success = true;
                    break;
                case ns.NakBind(reject):
                    delete reject;
                    break;
                case ns.ChannelClosed():
                    break;
            }

            if (!success) {
                DebugStub.Print("OpenVideo lookup of {0} failed.\n",
                                __arglist(devName));

                delete imp;
                delete ns;
                return null;
            }

            switch receive {
                case imp.Success():
                    break;
                case unsatisfiable:
                    throw new Exception("Didn't imp.RecvAckConnect");
                    break;
            }

            delete ns;
            return imp;
        }

        public static int Main(string[] args)
        {
            VideoDeviceContract.Imp video = OpenVideo("/dev/video");

            Console.WriteLine("Singularity Slide Show Viewer (PID={0})",
                              ProcessService.GetCurrentProcessId());

            if (video == null) {
                Console.WriteLine("Can only display slides on a graphic display.");
                return 1;
            }
            if (Slides.Content == null || Slides.Content.Length == 0) {
                Console.WriteLine("No slides to display.");
                delete video;
                return 1;
            }

            KeyboardDeviceContract.Imp keyboard = OpenKeyboard("/dev/keyboard");
            if (keyboard == null) {
                // TODO: show keyboardless slides with timer?
                delete video;
                return 1;
            }
            int slide = 0;

            byte[] currentSlide = (!)Slides.Content[slide];
            byte * opt(ExHeap[]) current = new[ExHeap] byte [currentSlide.Length];
            Bitter.FromByteArray(current, 0, currentSlide.Length,
                                 currentSlide, 0);
            video.SendFill(0, 0, 1023, 767, 0);
            video.RecvAckFill();
            video.SendBitBltBmp(32, 16, current);
            video.RecvAckBitBltBmp(out current);

            for (;;) {
                int x;
                int y;
                bool go_back = false;
                bool go_fore = false;
                bool go_home = false;
                bool go_end = false;

                uint key = 0;
                keyboard.SendGetKey();
                switch receive {
                    case keyboard.AckKey(ikey):
                        key = ikey;
                        break;
                    case keyboard.NakKey():
                        break;
                    case unsatisfiable:
                        throw new Exception("Didn't get reply from Keyboard");
                }

                if (key == 0) {
                    Tracing.Log(Tracing.Warning, "GetKey failed.");
                    break;
                }
                if ((key & (uint)Keyboard.Qualifiers.KEY_DOWN) == 0) {
                    continue;
                }
                if ((key & (uint)Keyboard.Qualifiers.KEY_MOUSE) == 0) {
                    char c = (char)(key & (uint)Keyboard.Qualifiers.KEY_BASE_CODE);

                    switch (c) {
                        case (char)Keyboard.Keys.ESCAPE:
                            delete video;
                            delete keyboard;
                            delete current;
                            return 0;
                        case (char)Keyboard.Keys.HOME:
                            go_home = true;
                            break;
                        case (char)Keyboard.Keys.UP_ARROW:
                        case (char)Keyboard.Keys.LEFT_ARROW:
                        case (char)Keyboard.Keys.PAGE_UP:
                        case '\b':
                            go_back = true;
                            break;
                        case (char)Keyboard.Keys.DOWN_ARROW:
                        case (char)Keyboard.Keys.RIGHT_ARROW:
                        case (char)Keyboard.Keys.PAGE_DOWN:
                        case '\n':
                        case ' ':
                            go_fore = true;
                            break;
                        case (char)Keyboard.Keys.END:
                            go_end = true;
                            break;
                        default:
                            continue;
                    }
                }
                else {
                    if ((key & (uint)Keyboard.Qualifiers.MOUSE_BUTTON_1) != 0) {
                        go_fore = true;
                    }
                    else if ((key & (uint)Keyboard.Qualifiers.MOUSE_BUTTON_0) != 0) {
                        go_back = true;
                    }
                    else {
                        continue;
                    }
                }

                if (go_home) {
                    slide = 0;
                }
                else if (go_fore) {
                    if (++slide >= Slides.Content.Length) {
                        slide = Slides.Content.Length - 1;
                    }
                }
                else if (go_back) {
                    if (--slide < 0) {
                        slide = 0;
                    }
                }
                else if (go_end) {
                    slide = Slides.Content.Length - 1;
                }


                if (Slides.Content.Length > 0) {
                    currentSlide = (!)Slides.Content[slide];
                    if (current.Length < currentSlide.Length) {
                        delete current;
                        current = new[ExHeap] byte [currentSlide.Length];
                    }
                    Bitter.FromByteArray(current, 0, currentSlide.Length,
                                         currentSlide, 0);
                    video.SendFill(0, 0, 1023, 767, 0);
                    video.RecvAckFill();
                    video.SendBitBltBmp(32, 16, current);
                    video.RecvAckBitBltBmp(out current);
                }
                else {
                    video.SendFill(0, 0, 1023, 767, 0);
                    video.RecvAckFill();
                }
            }
            delete keyboard;
            delete video;
            delete current;

            return 0;
        }
        public Pong()
        {
            svga = IoSystem.FindDeviceWithInterface(typeof(ISvgaDevice))
                as ISvgaDevice;
        }

        public void DrawPaddle(int paddle, bool erase)
        {
            svga.Fill(paddlesDrawX[paddle],
                      paddlesDrawY[paddle],
                      paddlesDrawX[paddle] + paddleWidth - 1,
                      paddlesDrawY[paddle] + paddleHeight - 1,
                      erase ? RGB.Black : RGB.Blue);
        }

        public void RedrawPaddle(int paddle)
        {
            if (paddlesDrawY[paddle] != (int) paddlesY[paddle]) {
                DrawPaddle(paddle, true);

                paddlesDrawY[paddle] = (int) paddlesY[paddle];

                DrawPaddle(paddle, false);
            }
        }

        public void MovePaddle(int paddle)
        {
            paddlesY[paddle] += GetPaddleState(paddle) * paddleSpeed;

            if (paddlesY[paddle] > paddleMax) {
                paddlesY[paddle] = paddleMax;
            }
            else if (paddlesY[paddle] < paddleMin) {
                paddlesY[paddle] = paddleMin;
            }

            RedrawPaddle(paddle);
        }

        public bool PaddleHit(int paddle)
        {
            return ((ballY > paddlesY[paddle] - ballSize) &&
                    (ballY < paddlesY[paddle] + paddleHeight));
        }

        public void ResetBall()
        {
            ballY = screenMinY + ((screenHeight - ballSize) / 2);
            ballAngle = (random.NextDouble() * ballStartAngle) -
                        (ballStartAngle / 2);

            if (lastWinner == 0) {
                ballX = ballMinX;
                if (ballAngle < 0) {
                    ballAngle += 2 * Math.PI;
                }
            }
            else {
                ballX = ballMaxX;
                ballAngle += Math.PI;
            }

            ballDrawX = (int) ballX;
            ballDrawY = (int) ballY;
        }

        public void DrawBall(bool erase)
        {
            svga.Fill(ballDrawX, ballDrawY,
                      ballDrawX + ballSize - 1, ballDrawY + ballSize - 1,
                      erase ? RGB.Black : RGB.Red);
        }

        public void RedrawBall()
        {
            if (ballDrawX != (int) ballX || ballDrawY != (int) ballY) {
                DrawBall(true);

                ballDrawX = (int) ballX;
                ballDrawY = (int) ballY;

                DrawBall(false);
            }
        }

        public void ReflectBallY(int line)
        {
            ballY = (2 * line) - ballY;
            ballAngle = (2 * Math.PI) - ballAngle;
        }

        public void SetAngle(int paddle)
        {
            // Find out where the ball hit the paddle, from -1 to 1.
            double ratio = ((ballY + (ballSize / 2)) -
                            (paddlesY[paddle] + (paddleHeight / 2))) /
                           ((paddleHeight + ballSize) / 2);

            // Set the new angle accordingly.
            ballAngle = ratio * ballMaxAngle;

            if (paddle == 0) {
                if (ballAngle < 0) {
                    ballAngle += 2 * Math.PI;
                }
            }
            else {
                ballAngle = Math.PI - ballAngle;
            }
        }

        public void MoveBall()
        {
            ballY += Math.Sin(ballAngle) * ballSpeed;
            if (ballY < ballMinY) {
                ReflectBallY(ballMinY);
            }
            else if (ballY > ballMaxY) {
                ReflectBallY(ballMaxY);
            }

            ballX += Math.Cos(ballAngle) * ballSpeed;
            if (ballX < ballMinX) {
                if (PaddleHit(0)) {
                    SetAngle(0);
                }
                else {
                    lastWinner = 1;
                    playing = false;
                }
            }
            else if (ballX > ballMaxX) {
                if (PaddleHit(1)) {
                    SetAngle(1);
                }
                else {
                    lastWinner = 0;
                    playing = false;
                }
            }

            RedrawBall();
        }

        public int GetPaddleState(int paddle)
        {
            int result;

            if (inputUp[paddle]) {
                result = -1;
            }
            else if (inputDown[paddle]) {
                result = 1;
            }
            else {
                result = 0;
            }

            return result;
        }

        public void SetStateFromChar(char c, bool @state)
        {
            switch (c) {
                case (char)Keyboard.Keys.UP_ARROW:
                    inputUp[1] = @state;
                    break;
                case (char)Keyboard.Keys.DOWN_ARROW:
                    inputDown[1] = @state;
                    break;
                case 'a':
                    inputUp[0] = @state;
                    break;
                case 'z':
                    inputDown[0] = @state;
                    break;
            }
        }

        public void GetInput(KeyboardDeviceContract.Imp keyboard)
        {
            uint key = 0;
            keyboard.SendPollKey();
            switch receive {
                case keyboard.AckKey(ikey):
                    key = ikey;
                    break;
                case keyboard.NakKey():
                    key = 0;
                    break;
                case unsatisfiable:
                    throw new Exception("Didn't get reply from Keyboard");
            }

            char c = (char) (key & (uint) Keyboard.Qualifiers.KEY_BASE_CODE);

            if ((key & (uint) Keyboard.Qualifiers.KEY_DOWN) != 0) {
                switch (c) {
                    case (char) Keyboard.Keys.ESCAPE:
                        done = true;
                        break;
                    case ' ':
                        if (!playing) {
                            ResetBall();
                            ClearScreen();
                            DrawPaddle(0, false);
                            DrawPaddle(1, false);
                            DrawBall(false);
                            playing = true;
                        }
                        break;
                    default:
                        SetStateFromChar(c, true);
                        break;
                }
            }
            else if ((key & (uint) Keyboard.Qualifiers.KEY_UP) != 0) {
                SetStateFromChar(c, false);
            }
        }

        public void FillScreen(RGB color)
        {
            svga.Fill(screenMinX, screenMinY, screenMaxX, screenMaxY, color);
        }

        public void ClearScreen()
        {
            FillScreen(RGB.Black);
        }

        public void FlashScreen()
        {
            FillScreen(RGB.Red);
            Sleep(1000);
            FillScreen(RGB.Green);
            Sleep(1000);
            FillScreen(RGB.Blue);
            Sleep(1000);
        }

        public void ShowMessage()
        {
            ClearScreen();

            for (int i = 0; i < 100; i++) {
                Console.WriteLine();
            }

            Console.Write("                                 ");
            Console.Write("Left: {0,-10}", scores[0]);
            Console.Write("                                 ");
            Console.Write("Right: {0,-10}", scores[1]);
            Console.WriteLine();
            Console.WriteLine();
            Console.Write("                                         ");
            Console.Write("Press space to begin or escape to quit...");
            Console.WriteLine();

            DrawPaddle(0, false);
            DrawPaddle(1, false);
            DrawBall(false);
        }

        public void Play()
        {
            KeyboardDeviceContract.Imp keyboard = Shell.OpenKeyboard("/dev/keyboard");

            Console.CursorHide();

            ShowMessage();

            while (!done) {
                GetInput(keyboard);

                if (playing) {
                    MovePaddle(0);
                    MovePaddle(1);
                    MoveBall();

                    if (!playing) {
                        scores[lastWinner]++;
                        FlashScreen();
                        ShowMessage();
                    }
                }

                Sleep(10);
            }

            ClearScreen();

            Console.CursorShow();
        }

        public void Sleep(int multiplier)
        {
            for (int j = 0; j < multiplier; j++) {
                for (int i = 0; i < 10000; i++) {
                    // Do nothing.
                }
            }
        }

        public static int Run(string[] args)
        {
            (new Pong()).Play();
            return 0;
        }
    }
}
