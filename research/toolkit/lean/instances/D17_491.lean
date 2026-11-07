import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 491 of the cap-17 certificate: slots 251392 .. 251903 -/
theorem chk_491 : chunkCheck 17 T stdSt 251392 512 = true := by decide +kernel

end Row17
