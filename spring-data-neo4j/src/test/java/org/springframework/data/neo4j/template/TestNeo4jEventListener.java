/*
 * Copyright (c)  [2011-2016] "Pivotal Software, Inc." / "Neo Technology" / "Graph Aware Ltd."
 *
 * This product is licensed to you under the Apache License, Version 2.0 (the "License").
 * You may not use this product except in compliance with the License.
 *
 * This product may include a number of subcomponents with
 * separate copyright notices and license terms. Your use of the source
 * code for these subcomponents is subject to the terms and
 * conditions of the subcomponent's license, as noted in the LICENSE file.
 *
 */

package org.springframework.data.neo4j.template;

import org.neo4j.ogm.session.event.Event;
import org.springframework.data.neo4j.events.ModificationEvent;

/**
 * Spring {@code ApplicationListener} used to capture {@link Event}s that occur during a test run.
 * Note that this is abstract because you're supposed to create an anonymous subclass to handle event type 'E' when you
 * use it.  This ensures Spring doesn't just send {@link Event}s to everything regardless.
 *
 * @author Adam George
 */
public abstract class TestNeo4jEventListener<E extends ModificationEvent> {

	private ModificationEvent event;

	public void onApplicationEvent(E event) {
		this.event = event;
	}

	public boolean hasReceivedAnEvent() {
		return this.event != null;
	}

	public ModificationEvent getEvent() {
		return event;
	}
}
