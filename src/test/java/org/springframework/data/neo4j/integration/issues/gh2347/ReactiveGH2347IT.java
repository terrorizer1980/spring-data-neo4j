/*
 * Copyright 2011-2021 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.springframework.data.neo4j.integration.issues.gh2347;

import reactor.test.StepVerifier;

import java.util.Collections;

import org.junit.jupiter.api.Test;
import org.neo4j.driver.Driver;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.data.neo4j.config.AbstractReactiveNeo4jConfig;
import org.springframework.data.neo4j.repository.ReactiveNeo4jRepository;
import org.springframework.data.neo4j.repository.config.EnableReactiveNeo4jRepositories;
import org.springframework.data.neo4j.test.Neo4jIntegrationTest;
import org.springframework.transaction.annotation.EnableTransactionManagement;

/**
 * @author Michael J. Simons
 */
@Neo4jIntegrationTest
class ReactiveGH2347IT extends TestBase {

	@Test
	void entitiesWithAssignedIdsSavedInBatchMustBeIdentifiableWithTheirInternalIds(
			@Autowired ApplicationRepository applicationRepository,
			@Autowired Driver driver
	) {
		applicationRepository
				.saveAll(Collections.singletonList(createData()))
				.as(StepVerifier::create)
				.expectNextCount(1L)
				.verifyComplete();

		assertDatabase(driver);
	}

	@Test
	void entitiesWithAssignedIdsMustBeIdentifiableWithTheirInternalIds(
			@Autowired ApplicationRepository applicationRepository,
			@Autowired Driver driver
	) {
		applicationRepository
				.save(createData())
				.as(StepVerifier::create)
				.expectNextCount(1L)
				.verifyComplete();
		assertDatabase(driver);
	}

	interface ApplicationRepository extends ReactiveNeo4jRepository<Application, String> {
	}

	@Configuration
	@EnableTransactionManagement
	@EnableReactiveNeo4jRepositories(considerNestedRepositories = true)
	static class Config extends AbstractReactiveNeo4jConfig {

		@Bean
		public Driver driver() {

			return neo4jConnectionSupport.getDriver();
		}
	}
}
