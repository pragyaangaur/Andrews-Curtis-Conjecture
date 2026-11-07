import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 97 of the cap-17 certificate: slots 49664 .. 50175 -/
theorem chk_97 : chunkCheck 17 T stdSt 49664 512 = true := by decide +kernel

end Row17
