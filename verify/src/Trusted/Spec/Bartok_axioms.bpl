//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

//////////////////////////////////////////////////////////////////////////////
// BARTOK INTERFACE
//////////////////////////////////////////////////////////////////////////////

axiom (forall abs:int, vt:int::{TVT(abs, vt)} VTable(abs, vt) ==>
    inRo(vt + ?VT_MASK, 4)
 && inRo(vt + ?VT_BASE_LENGTH, 4)
 && inRo(vt + ?VT_ARRAY_ELEMENT_SIZE, 4)
 && inRo(vt + ?VT_ARRAY_ELEMENT_CLASS, 4)
 && inRo(vt + ?VT_ARRAY_OF, 4)
);

axiom (forall l:$FrameLayout, j:int::{TVF(l),TO(j)}
    (inFrame(l, 0) && !frameHasPtr(l, 0))
 && (inFrame(l, 1) && !frameHasPtr(l, 1))
 && (TO(j) && frameHasPtr(l, j) ==> inFrame(l, j))
 && (TO(j) && getBit(frameDescriptor(l), 0) && !getBit(frameDescriptor(l), 1) && and(shr(frameDescriptor(l), 6), 1023) == 0 ==>
        between(0, 16, frameLayoutArgs(l))
     && frameLayoutArgs(l) == and(shr(frameDescriptor(l), 2), 15)
     && (frameHasPtr(l, j) ==> 0 <= frameLayoutArgs(l) + 1 - j && frameLayoutArgs(l) - 1 - j < 16)
     && (0 <= frameLayoutArgs(l) + 1 - j && frameLayoutArgs(l) - 1 - j < 16 ==> (
            (j >= 2 ==> frameHasPtr(l, j) == getBit(frameDescriptor(l), 16 + frameLayoutArgs(l) + 1 - j))
         && (j < 0  ==> frameHasPtr(l, j) == getBit(frameDescriptor(l), 16 + frameLayoutArgs(l) - 1 - j)))
    ))
 && (TO(j) && !getBit(frameDescriptor(l), 0) ==> inRo(frameDescriptor(l), 4))
 && (TO(j) && !getBit(frameDescriptor(l), 0) && ro32(frameDescriptor(l)) == 4096 && inFrame(l, j) ==> (
        inRo(frameDescriptor(l) + 4, 1)
     && inRo(frameDescriptor(l) + 6 + frameFieldToSlot(l, j), 1)
     && j == roS8(frameDescriptor(l) + 6 + frameFieldToSlot(l, j))
     && frameHasPtr(l, j) == (
          between(0, roU8(frameDescriptor(l) + 4), frameFieldToSlot(l, j))
        )
    )));

axiom (forall l:$FrameLayout, k:int::{TVF(l),TSlot(k)}
        TSlot(k) && !getBit(frameDescriptor(l), 0) && ro32(frameDescriptor(l)) == 4096 && between(0, roU8(frameDescriptor(l) + 4), k) ==>
            inFrame(l, roS8(frameDescriptor(l) + 6 + k))
         && k == frameFieldToSlot(l, roS8(frameDescriptor(l) + 6 + k))
    );

axiom (forall s:int, j:int::{TVS(s, j)}
        0 <= s && s < ?sectionCount && 0 <= j ==>
            inRo(?dataSectionBase + 4 * s, 4)
         && inRo(?dataSectionEnd + 4 * s, 4)
         && inRo(?staticDataPointerBitMap + 4 * s, 4)
         && (sectionBase(s) + 4 * j < sectionEnd(s) ==>
                inSectionData(ro32(?dataSectionBase + 4 * s) + 4 * j)
             && inRo(ro32(?staticDataPointerBitMap + 4 * s) + 4 * shr(j, 5), 4)
             && and(j, 31) < 32 // REVIEW: this is true, so just prove it
             && sectionHasPtr(s, j) == getBit(
                  ro32(ro32(?staticDataPointerBitMap + 4 * s) + 4 * shr(j, 5)),
                  and(j, 31)
                  )));

axiom (forall f:int::{TVFT(f)}
(
  (forall t:int::{TT(t)} TT(t) ==> 0 <= t && t < ?callSiteTableCount ==>
      inRo(?codeBaseStartTable + 4 * t, 4)
   && inRo(?returnAddressToCallSiteSetNumbers + 4 * t, 4)
   && inRo(?callSiteSetCount + 4 * t, 4)
   && inRo(ro32(?callSiteSetCount + 4 * t), 4)
   && inRo(?callSiteSetNumberToIndex + 4 * t, 4)
   && inRo(?activationDescriptorTable + 4 * t, 4)
   && (forall j:int::{TO(j)} TO(j) ==> 0 <= j && j <= ro32(ro32(?callSiteSetCount + 4 * t)) ==>
          inRo(ro32(?returnAddressToCallSiteSetNumbers + 4 * t) + 4 * j, 4)
       && inRo(ro32(?callSiteSetNumberToIndex + 4 * t) + 2 * j, 2)
       && inRo(ro32(?activationDescriptorTable + 4 * t)
            + 4 * roU16(ro32(?callSiteSetNumberToIndex + 4 * t) + 2 * j), 4)
      )
  )
));

axiom (forall f:int::{TVFT(f)}
(
  (forall t:int, j1:int, j2:int::{TT(t), TO(j1), TO(j2)} TT(t) && TO(j1) && TO(j2) ==>
    0 <= t && t < ?callSiteTableCount && 0 <= j1 && j1 < j2 && j2 <= ro32(ro32(?callSiteSetCount + 4 * t)) ==>
      ro32(ro32(?returnAddressToCallSiteSetNumbers + 4 * t) + 4 * j1) < ro32(ro32(?returnAddressToCallSiteSetNumbers + 4 * t) + 4 * j2)
  )
));

