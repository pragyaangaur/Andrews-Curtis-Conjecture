import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 321 of the cap-17 certificate: slots 164352 .. 164863 -/
theorem chk_321 : chunkCheck 17 T stdSt 164352 512 = true := by decide +kernel

end Row17
