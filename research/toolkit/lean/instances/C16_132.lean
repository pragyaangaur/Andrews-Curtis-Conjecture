import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 132 of the cap-16 certificate: slots 135168 .. 136191 -/
theorem chk_132 : chunkCheck 16 T stdSt 135168 1024 = true := by decide +kernel

end Row16
