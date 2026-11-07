import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 112 of the cap-17 certificate: slots 57344 .. 57855 -/
theorem chk_112 : chunkCheck 17 T stdSt 57344 512 = true := by decide +kernel

end Row17
