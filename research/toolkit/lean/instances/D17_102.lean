import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 102 of the cap-17 certificate: slots 52224 .. 52735 -/
theorem chk_102 : chunkCheck 17 T stdSt 52224 512 = true := by decide +kernel

end Row17
