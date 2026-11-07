import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 160 of the cap-16 certificate: slots 163840 .. 164863 -/
theorem chk_160 : chunkCheck 16 T stdSt 163840 1024 = true := by decide +kernel

end Row16
