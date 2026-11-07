import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 161 of the cap-16 certificate: slots 164864 .. 165887 -/
theorem chk_161 : chunkCheck 16 T stdSt 164864 1024 = true := by decide +kernel

end Row16
