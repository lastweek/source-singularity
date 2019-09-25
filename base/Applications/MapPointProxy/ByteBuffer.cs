// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;

public class ByteBuffer
{
	private byte[] fData;
	private int fSize; // Amount of fData actually available to the user

	public ByteBuffer(int initialSize)
	{
		fData = new byte[initialSize];
		fSize = initialSize;
	}

	public ByteBuffer()
	{
	}

	public void EnsureSize(int overallSize)
	{
		// Asking for less space than you have does nothing
		if (overallSize < fSize)
		{
			return;
		}

		// Asking for zero when we're empty does nothing
		if (overallSize == 0)
		{
			return;
		}

		if ((fData == null) || (fData.Length < overallSize))
		{
			// Not enough room in our current array. Double until we're big enough.
			int newSize = (fData == null) ? overallSize : fData.Length;
			while (newSize < overallSize) {
			    newSize *= 2;
			}
			byte[] newBuffer = new byte[newSize];

			if (fData != null)
			{
				int bytesToCopy = overallSize < fSize ? overallSize : fSize;
				Buffer.BlockCopy(fData, 0, newBuffer, 0, bytesToCopy);
			}

			fData = newBuffer;
		}

		fSize = overallSize;
	}

	public void Add(byte[] newData, int offset, int length)
	{
		int previousSize = fSize;
		EnsureSize(previousSize + length);
		Buffer.BlockCopy(newData, offset, fData, previousSize, length);
	}

	public void Add(byte newByte)
	{
		int previousSize = fSize;
		EnsureSize(previousSize + 1);
		fData[previousSize] = newByte;
	}

	// WARNING; Do not rely on this being accessible across calls to
	// Add() or EnsureSize()!! Do not index out of bounds!! UNSAFE!
	public byte[] UnderlyingBuffer
	{
		get { return fData; }
	}

	public byte[] TrimAndCopy(int trimLength)
	{
		return TrimAndCopy(0, trimLength);
	}

	public byte[] TrimAndCopy(int offset, int trimLength)
	{
		byte[] retval = new byte[trimLength];
		Buffer.BlockCopy(fData, offset, retval, 0, trimLength);
		return retval;
	}

	public int Size
	{
		get
		{
			if (fData != null)
			{
				return fSize;
			}
			else {
				return 0;
			}
		}
	}

	public byte this[int index]
	{
		get 
		{
			ValidateIndex(index);
			return fData[index];
		}

		set
		{
			ValidateIndex(index);
			fData[index] = value;
		}
	}

	private void ValidateIndex(int index)
	{
		if (fData == null)
		{
			throw new IndexOutOfRangeException("Buffer currently empty");
		}

		if ((index < 0) || (index >= fSize))
		{
			throw new IndexOutOfRangeException();
		}
	}
}
