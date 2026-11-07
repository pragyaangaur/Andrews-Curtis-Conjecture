import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 163 of the cap-17 certificate: slots 83456 .. 83967 -/
theorem chk_163 : chunkCheck 17 T stdSt 83456 512 = true := by decide +kernel

end Row17
